import Magma.FactorizationStore

/-!
# The Kamea Reference Runner (supplementary)

Differential-testing support for the Rust host
(`kamea-machine`, Phase 1): this file makes the **certified machine
itself** executable as a reference oracle, so the Rust transliteration
can be fuzzed against it demanding bit-identical results.

Two parts:

* **Certified**: `loopFull`, a driver loop that also reports the final
  store (the certified `loop` discards σ at the halt cut), together
  with `loopFull_agrees`: its value component *is* the certified
  loop's answer at every fuel. So the oracle's observable behaviour is
  pinned to the certified semantics by theorem, and the store report
  is an extra observation on top.
* **Uncertified plumbing** (`partial`, no theorems): a token
  parser/printer for programs, values, continuations, and stores, and
  an `IO` main. A parser bug cannot silently corrupt the audit: the
  runner echoes the parsed program back in canonical form and the
  harness diffs the echo against its own encoding.

Usage (from the repo root; the Rust side's `scripts/difftest.sh`
drives this):

    lake env lean --run Magma/KameaRef.lean < cases.txt

Case line: `<id> <fuel> <prog tokens…>`; result line:
`<id> <fuel> <prog echo> => none` or `… => some <VAL> | S<n> <VAL>…`.
Token grammar (shared with `kamea-diff` on the Rust side):

    PROG ::= a<k> | v<n> | l PROG | @ PROG PROG | k PROG
           | r PROG | d PROG | s PROG PROG
    VAL  ::= E<k> | C VAL VAL | F PROG ENV | X KONT | L<n>
    ENV  ::= G<n> VAL*        KONT ::= H | AL PROG ENV KONT
                                     | AR VAL KONT | RK KONT | DK KONT
                                     | SL PROG ENV KONT | SR VAL KONT
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationStore

/-- The store held by a state. -/
def stateStore : State → Store
  | .eval _ _ σ _ => σ
  | .ret _ σ _ => σ

/-- The driver loop, also reporting the final store. -/
def loopFull : Nat → State → Option (Val × Store)
  | 0, _ => none
  | fuel + 1, s =>
    match step s with
    | .inl s' => loopFull fuel s'
    | .inr v => some (v, stateStore s)

/-- **The oracle is the certified machine**: `loopFull`'s value
    component agrees with the certified `loop` at every fuel and
    state. -/
theorem loopFull_agrees : ∀ (n : Nat) (s : State),
    (loopFull n s).map Prod.fst = loop n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ m ih =>
    intro s
    simp only [loopFull, loop]
    cases step s with
    | inl s' => simpa using ih s'
    | inr v => rfl

end FactorizationStore

namespace KameaRef

open FactorizationStore

-- Printers (uncertified plumbing; grammar shared with kamea-diff).

partial def progS : Prog → String
  | .atom a => s!"a{a.val}"
  | .var n => s!"v{n}"
  | .lam b => s!"l {progS b}"
  | .app f x => s!"@ {progS f} {progS x}"
  | .callcc b => s!"k {progS b}"
  | .ref e => s!"r {progS e}"
  | .deref e => s!"d {progS e}"
  | .setref l e => s!"s {progS l} {progS e}"

mutual
  partial def valS : Val → String
    | .elem a => s!"E{a.val}"
    | .cell u v => s!"C {valS u} {valS v}"
    | .clos b ρ => s!"F {progS b} {envS ρ}"
    | .cont k => s!"X {kontS k}"
    | .loc n => s!"L{n}"

  partial def envS (ρ : List Val) : String :=
    s!"G{ρ.length}" ++ String.join (ρ.map (fun v => " " ++ valS v))

  partial def kontS : Kont → String
    | .halt => "H"
    | .appL x ρ k => s!"AL {progS x} {envS ρ} {kontS k}"
    | .appR v k => s!"AR {valS v} {kontS k}"
    | .refK k => s!"RK {kontS k}"
    | .derefK k => s!"DK {kontS k}"
    | .setL e ρ k => s!"SL {progS e} {envS ρ} {kontS k}"
    | .setR v k => s!"SR {valS v} {kontS k}"
end

partial def storeS (σ : Store) : String :=
  s!"S{σ.length}" ++ String.join (σ.map (fun v => " " ++ valS v))

-- Parser (uncertified plumbing; the echo makes skew visible).

partial def parseP (ts : Array String) (i : Nat) : Option (Prog × Nat) := do
  let tok ← ts[i]?
  if tok.startsWith "a" then
    let n ← (tok.drop 1).toNat?
    if h : n < 8 then some (.atom ⟨n, h⟩, i + 1) else none
  else if tok.startsWith "v" then
    let n ← (tok.drop 1).toNat?
    some (.var n, i + 1)
  else if tok = "l" then
    let (b, j) ← parseP ts (i + 1)
    some (.lam b, j)
  else if tok = "@" then
    let (f, j) ← parseP ts (i + 1)
    let (x, j2) ← parseP ts j
    some (.app f x, j2)
  else if tok = "k" then
    let (b, j) ← parseP ts (i + 1)
    some (.callcc b, j)
  else if tok = "r" then
    let (e, j) ← parseP ts (i + 1)
    some (.ref e, j)
  else if tok = "d" then
    let (e, j) ← parseP ts (i + 1)
    some (.deref e, j)
  else if tok = "s" then
    let (l, j) ← parseP ts (i + 1)
    let (e, j2) ← parseP ts j
    some (.setref l e, j2)
  else none

/-- Run one case on the certified machine (empty env, empty store). -/
def runCase (fuel : Nat) (p : Prog) : String :=
  match loopFull fuel (.eval p [] [] .halt) with
  | none => "none"
  | some (v, σ) => s!"some {valS v} | {storeS σ}"

partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let content ← stdin.readToEnd
  for line in content.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.isEmpty then
      continue
    let ts := (l.splitOn " ").toArray
    match ts[0]?, ts[1]? with
    | some id, some fs =>
      match fs.toNat? with
      | some fuel =>
        match parseP ts 2 with
        | some (p, _) =>
          IO.println s!"{id} {fuel} {progS p} => {runCase fuel p}"
        | none => IO.println s!"{id} PARSE-ERROR"
      | none => IO.println s!"{id} FUEL-ERROR"
    | _, _ => IO.println "LINE-ERROR"

end KameaRef
end Dichotomic

/-- Entry point for `lake env lean --run Magma/KameaRef.lean`. -/
def main : IO Unit := Dichotomic.KameaRef.main

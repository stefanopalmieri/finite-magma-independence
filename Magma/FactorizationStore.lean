import Magma.FactorizationCtrl

/-!
# Factorization with the Store: CESK, Completed

The final extension rung of `MACHINE.md` §9: **the store**. The machine
gains the S of CESK — a heap of locations threaded through every step —
and with it all four components of the architecture decided in
`MACHINE.md` are inhabited, each having arrived on exactly the rung
whose theorem demanded it: C and K on the control rung, E on the
environment rung, S here.

The structural fact this rung certifies is the asymmetry between E and
S: **environments are captured, the store is threaded**. Closures carry
their environment and never a store; every machine step carries the one
store forward. Two consequences are theorems:

* mutation is observable through β (`eval_quote_mutation`: a `setref`
  performed in an argument is seen by the function body — the store
  arrived there by threading, since no environment connects them);
* continuations do **not** restore the store (`step_throw`: the σ on
  both sides of the throw rule is the same σ) — R7RS's semantics for
  `call/cc` + mutation, as one `rfl`.

The factorization theorem is unchanged once more:

    evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p    (uniformly in fuel)

base case still `eatom_qatom`. Locations, like closures and
continuations, are rejected by `decodeD`: store objects are semantic,
not syntactic — nothing about the heap can be written or read back,
so representation adequacy stays static.

**Conservativity is now a lockstep bisimulation** (`step_embed`): on
store-free programs the machine, carrying any store σ, steps in exact
lockstep with the control machine and never touches σ. At the loop
level this gives `runM_embed` — equality of the two machines' answers
under `Option.map`, covering values *and* divergence in one equation
(no determinism argument needed) — from which Ω's divergence transfers
for free (`Omega_still_diverges`).

Tags: the store forms share data? (element 5) — store operations are
the making, reading, and rewriting of data — discriminated by the
operator trio as sub-tags: quote (2) for `ref` (allocation suspends a
value into the heap), eval (3) for `deref` (retrieval), shift (4) for
`setref` (rewriting in place). Tag values are engineering
(`MACHINE.md` §8); the necessity of tags is not.

With this rung, §9 item 1 closes: the two-level factorization theorem
holds over the full CESK machine, every rung conservative over the
last, every induction grounded in the same certified table law. What
remains toward R7RS (§6) is breadth, not architecture: data types,
the numeric tower, `syntax-rules`, ports — tape and driver
engineering with no new algebraic content.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationStore

open Factorization (qatom eatom eatom_qatom)

/-- Programs: instructions, variables, abstraction, application, μ,
    and the three store forms — allocate, read, write. -/
inductive Prog where
  | atom   : Fin 8 → Prog
  | var    : Nat → Prog
  | lam    : Prog → Prog
  | app    : Prog → Prog → Prog
  | callcc : Prog → Prog
  | ref    : Prog → Prog
  | deref  : Prog → Prog
  | setref : Prog → Prog → Prog
deriving DecidableEq

mutual
  /-- Tape values: elements, heap cells, closures, reified
      continuations, and locations. -/
  inductive Val where
    | elem : Fin 8 → Val
    | cell : Val → Val → Val
    | clos : Prog → List Val → Val
    | cont : Kont → Val
    | loc  : Nat → Val

  /-- Continuations: the control frames plus the three store frames. -/
  inductive Kont where
    | halt   : Kont
    | appL   : Prog → List Val → Kont → Kont
    | appR   : Val → Kont → Kont
    | refK   : Kont → Kont
    | derefK : Kont → Kont
    | setL   : Prog → List Val → Kont → Kont
    | setR   : Val → Kont → Kont
end

/-- Environments: captured by closures. -/
abbrev Env := List Val

/-- The store: threaded through every step, captured by nothing. -/
abbrev Store := List Val

/-- Machine states: commands ⟨focus ‖ store ‖ continuation⟩. -/
inductive State where
  | eval : Prog → Env → Store → Kont → State
  | ret  : Val → Store → Kont → State

/-- One machine step. Instructions still cost one table lookup;
    allocation appends (fresh address = current length), reading
    indexes, writing updates in place; errors cut to the halt
    channel. -/
def step : State → State ⊕ Val
  | .eval (.atom a) _ σ k => .inl (.ret (.elem a) σ k)
  | .eval (.var n) ρ σ k => .inl (.ret (ρ.getD n (.elem 0)) σ k)
  | .eval (.lam b) ρ σ k => .inl (.ret (.clos b ρ) σ k)
  | .eval (.app f x) ρ σ k => .inl (.eval f ρ σ (.appL x ρ k))
  | .eval (.callcc b) ρ σ k => .inl (.eval b (.cont k :: ρ) σ k)
  | .eval (.ref e) ρ σ k => .inl (.eval e ρ σ (.refK k))
  | .eval (.deref e) ρ σ k => .inl (.eval e ρ σ (.derefK k))
  | .eval (.setref l e) ρ σ k => .inl (.eval l ρ σ (.setL e ρ k))
  | .ret v _ .halt => .inr v
  | .ret v σ (.appL x ρ k) => .inl (.eval x ρ σ (.appR v k))
  | .ret v σ (.appR (.clos b ρ') k) => .inl (.eval b (v :: ρ') σ k)
  | .ret v σ (.appR (.cont k') _) => .inl (.ret v σ k')
  | .ret (.elem b) σ (.appR (.elem a) k) => .inl (.ret (.elem (dotA8 a b)) σ k)
  | .ret _ σ (.appR (.elem _) k) => .inl (.ret (.elem 0) σ k)
  | .ret _ σ (.appR _ k) => .inl (.ret (.elem 0) σ k)
  | .ret v σ (.refK k) => .inl (.ret (.loc σ.length) (σ ++ [v]) k)
  | .ret (.loc n) σ (.derefK k) => .inl (.ret (σ.getD n (.elem 0)) σ k)
  | .ret _ σ (.derefK k) => .inl (.ret (.elem 0) σ k)
  | .ret v σ (.setL e ρ k) => .inl (.eval e ρ σ (.setR v k))
  | .ret w σ (.setR (.loc n) k) => .inl (.ret w (σ.set n w) k)
  | .ret _ σ (.setR _ k) => .inl (.ret (.elem 0) σ k)

/-- **Allocation**: a fresh location — the current length — and the
    store grows by one. -/
theorem step_alloc (v : Val) (σ : Store) (k : Kont) :
    step (.ret v σ (.refK k)) =
      .inl (.ret (.loc σ.length) (σ ++ [v]) k) := rfl

/-- **Reading** indexes the store and leaves it unchanged. -/
theorem step_read (n : Nat) (σ : Store) (k : Kont) :
    step (.ret (.loc n) σ (.derefK k)) =
      .inl (.ret (σ.getD n (.elem 0)) σ k) := rfl

/-- **Writing** updates in place; the written value is returned. -/
theorem step_write (w : Val) (n : Nat) (σ : Store) (k : Kont) :
    step (.ret w σ (.setR (.loc n) k)) =
      .inl (.ret w (σ.set n w) k) := rfl

/-- **Continuations do not restore the store**: the σ on both sides of
    the throw rule is the same σ. Jumping backward through a captured
    continuation does not undo mutations — R7RS's `call/cc` + `set!`
    semantics, as one `rfl`. -/
theorem step_throw (v : Val) (σ : Store) (k' k : Kont) :
    step (.ret v σ (.appR (.cont k') k)) = .inl (.ret v σ k') := rfl

set_option linter.unnecessarySimpa false in
/-- A fresh allocation reads back: the address handed out by
    `step_alloc` indexes the value just stored. -/
theorem read_alloc (σ : Store) (v : Val) :
    (σ ++ [v]).getD σ.length (.elem 0) = v := by
  induction σ with
  | nil => rfl
  | cons u σ ih => simpa using ih

/-- The driver loop. -/
def loop : Nat → State → Option Val
  | 0, _ => none
  | fuel + 1, s =>
    match step s with
    | .inl s' => loop fuel s'
    | .inr v => some v

/-- Run a program with an initial store. -/
def runM (fuel : Nat) (ρ : Env) (σ : Store) (p : Prog) : Option Val :=
  loop fuel (.eval p ρ σ .halt)

theorem loop_mono {n : Nat} {s : State} {w : Val} (h : loop n s = some w) :
    loop (n + 1) s = some w := by
  induction n generalizing s with
  | zero => simp [loop] at h
  | succ m ih =>
    simp only [loop] at h ⊢
    cases hs : step s with
    | inl s' => rw [hs] at h; exact ih h
    | inr v => rw [hs] at h; exact h

theorem loop_mono_le {n n' : Nat} (hle : n ≤ n') {s : State} {w : Val}
    (h : loop n s = some w) : loop n' s = some w := by
  induction hle with
  | refl => exact h
  | step _ ih => exact loop_mono ih

theorem loop_det {n n' : Nat} {s : State} {w w' : Val}
    (h : loop n s = some w) (h' : loop n' s = some w') : w = w' := by
  rcases Nat.le_total n n' with hle | hle
  · rw [loop_mono_le hle h] at h'
    exact Option.some.inj h'
  · rw [loop_mono_le hle h'] at h
    exact (Option.some.inj h).symm

/-- De Bruijn indices on the tape: unary shift-cell numerals. -/
def natToVal : Nat → Val
  | 0 => .elem 0
  | n + 1 => .cell (.elem 4) (natToVal n)

def valToNat : Val → Option Nat
  | .elem b => if b = (0 : Fin 8) then some 0 else none
  | .cell (.elem h) t => if h = (4 : Fin 8) then (valToNat t).map (· + 1) else none
  | _ => none

theorem valToNat_natToVal : ∀ n : Nat, valToNat (natToVal n) = some n := by
  intro n
  induction n with
  | zero => simp [natToVal, valToNat]
  | succ n ih => simp [natToVal, valToNat, ih]

/-- Driver-level quote. Atoms through the table's duality; compound
    tags: quote (2) λ, eval (3) app, shift (4) var, data? (5) store
    forms — sub-tagged by the operator trio: quote/`ref`, eval/`deref`,
    shift/`setref` — judge? (6) μ. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .var n => .cell (.elem 4) (natToVal n)
  | .lam b => .cell (.elem 2) (quoteD b)
  | .app f x => .cell (.elem 3) (.cell (quoteD f) (quoteD x))
  | .callcc b => .cell (.elem 6) (quoteD b)
  | .ref e => .cell (.elem 5) (.cell (.elem 2) (quoteD e))
  | .deref e => .cell (.elem 5) (.cell (.elem 3) (quoteD e))
  | .setref l e => .cell (.elem 5) (.cell (.elem 4) (.cell (quoteD l) (quoteD e)))

mutual
  /-- Driver-level decode. Closures, continuations, and locations are
      rejected: procedures, consumers, and store objects are
      first-class values but never data. -/
  def decodeD : Val → Option Prog
    | .elem b => some (.atom (eatom b))
    | .cell (.elem h) rest =>
      if h = (2 : Fin 8) then (decodeD rest).map .lam
      else if h = (3 : Fin 8) then decodeApp rest
      else if h = (4 : Fin 8) then (valToNat rest).map .var
      else if h = (5 : Fin 8) then decodeStore rest
      else if h = (6 : Fin 8) then (decodeD rest).map .callcc
      else none
    | _ => none

  /-- Reading the payload of an application quotation. -/
  def decodeApp : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some f, some x => some (.app f x)
      | _, _ => none
    | _ => none

  /-- Reading a store-form quotation: dispatch on the sub-tag. -/
  def decodeStore : Val → Option Prog
    | .cell (.elem d) rest =>
      if d = (2 : Fin 8) then (decodeD rest).map .ref
      else if d = (3 : Fin 8) then (decodeD rest).map .deref
      else if d = (4 : Fin 8) then decodeSet rest
      else none
    | _ => none

  /-- Reading a `setref` quotation's payload pair. -/
  def decodeSet : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some l, some e => some (.setref l e)
      | _, _ => none
    | _ => none
end

/-- User-level eval: the expression representation and the environment
    are its arguments; the store is the machine's, threaded through the
    call like any other step — eval does not snapshot it. -/
def evalD (fuel : Nat) (ρ : Env) (σ : Store) (v : Val) : Option Val :=
  match decodeD v with
  | some p => runM fuel ρ σ p
  | none => some (.elem 0)

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, still static**: no environment, no fuel,
    no continuation, no store. Base case: the certified table law
    `eatom_qatom`. -/
theorem decode_quote (p : Prog) : decodeD (quoteD p) = some p := by
  induction p with
  | atom a => simp [quoteD, decodeD, eatom_qatom]
  | var n => simp [quoteD, decodeD, valToNat_natToVal]
  | lam b ih => simp [quoteD, decodeD, ih]
  | app f x ihf ihx => simp [quoteD, decodeD, decodeApp, ihf, ihx]
  | callcc b ih => simp [quoteD, decodeD, ih]
  | ref e ih => simp [quoteD, decodeD, decodeStore, ih]
  | deref e ih => simp [quoteD, decodeD, decodeStore, ih]
  | setref l e ihl ihe =>
    simp [quoteD, decodeD, decodeStore, decodeSet, ihl, ihe]

/-- **The factorization theorem over the full CESK machine**: uniformly
    in fuel, `eval fuel ρ σ (quote p) = runM fuel ρ σ p`. -/
theorem eval_quote (fuel : Nat) (ρ : Env) (σ : Store) (p : Prog) :
    evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p := by
  simp [evalD, decode_quote]

/-- Allocate, then read back, through quotation: `deref (ref a)` is
    `a`. -/
theorem eval_quote_ref_roundtrip (a : Fin 8) :
    evalD 8 [] [] (quoteD (.deref (.ref (.atom a)))) = some (.elem a) := by
  rw [eval_quote]; rfl

/-- **Mutation observed through β**: allocate a box holding `data?`
    (5), pass it to a function that overwrites it with `judge?` (6) in
    argument position and then reads it in the body. The write is seen
    by the read although no environment connects them — the store
    arrived by threading. E captured, S threaded, as a computation. -/
theorem eval_quote_mutation :
    evalD 24 [] []
      (quoteD (.app
        (.lam (.app (.lam (.deref (.var 1)))
                    (.setref (.var 0) (.atom 6))))
        (.ref (.atom 5)))) = some (.elem 6) := by
  rw [eval_quote]; rfl

/-- The control rung embeds: its programs are the store-free ones. -/
def embed : FactorizationCtrl.Prog → Prog
  | .atom a => .atom a
  | .var n => .var n
  | .lam b => .lam (embed b)
  | .app f x => .app (embed f) (embed x)
  | .callcc b => .callcc (embed b)

mutual
  /-- Its values embed — no locations ever arise from them. -/
  def embedVal : FactorizationCtrl.Val → Val
    | .elem a => .elem a
    | .cell u v => .cell (embedVal u) (embedVal v)
    | .clos b ρ => .clos (embed b) (embedEnv ρ)
    | .cont k => .cont (embedKont k)

  def embedEnv : List FactorizationCtrl.Val → List Val
    | [] => []
    | v :: ρ => embedVal v :: embedEnv ρ

  def embedKont : FactorizationCtrl.Kont → Kont
    | .halt => .halt
    | .appL x ρ k => .appL (embed x) (embedEnv ρ) (embedKont k)
    | .appR v k => .appR (embedVal v) (embedKont k)
end

/-- A control-machine state, placed beside an arbitrary store. -/
def embedState (σ : Store) : FactorizationCtrl.State → State
  | .eval p ρ k => .eval (embed p) (embedEnv ρ) σ (embedKont k)
  | .ret v k => .ret (embedVal v) σ (embedKont k)

theorem getD_embedEnv (ρ : FactorizationCtrl.Env) (n : Nat) :
    (embedEnv ρ)[n]?.getD (Val.elem 0) =
      embedVal (ρ[n]?.getD (.elem 0)) := by
  induction ρ generalizing n with
  | nil => simp [embedEnv, embedVal]
  | cons u ρ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simpa [embedEnv] using ih m

set_option linter.unusedSimpArgs false in
/-- **The lockstep bisimulation**: on store-free programs the machine,
    carrying any store σ, performs exactly the control machine's step
    and never touches σ. -/
theorem step_embed (σ : Store) (s : FactorizationCtrl.State) :
    step (embedState σ s) =
      (FactorizationCtrl.step s).map (embedState σ) embedVal := by
  cases s with
  | eval p ρ k =>
    cases p <;>
      simp [embedState, embed, embedVal, embedEnv, embedKont, step,
        FactorizationCtrl.step, getD_embedEnv]
  | ret v k =>
    cases k with
    | halt =>
      simp [embedState, embedKont, step, FactorizationCtrl.step]
    | appL x ρ k =>
      simp [embedState, embedKont, step, FactorizationCtrl.step]
    | appR u k =>
      cases u <;> cases v <;>
        simp [embedState, embed, embedVal, embedEnv, embedKont, step,
          FactorizationCtrl.step]

/-- Lockstep at the loop level: identical answers under `Option.map`,
    covering values and divergence in one equation. -/
theorem loop_embed (n : Nat) (σ : Store) (s : FactorizationCtrl.State) :
    loop n (embedState σ s) = (FactorizationCtrl.loop n s).map embedVal := by
  induction n generalizing s with
  | zero => rfl
  | succ m ih =>
    simp only [loop, FactorizationCtrl.loop, step_embed]
    cases FactorizationCtrl.step s with
    | inl s' => simpa using ih s'
    | inr v => rfl

/-- **Conservativity**: with any store, on a store-free program, the
    CESK machine's answer is exactly the control machine's — value or
    divergence alike. -/
theorem runM_embed (fuel : Nat) (σ : Store) (ρ : FactorizationCtrl.Env)
    (p : FactorizationCtrl.Prog) :
    runM fuel (embedEnv ρ) σ (embed p) =
      (FactorizationCtrl.runM fuel ρ p).map embedVal := by
  simpa [runM, FactorizationCtrl.runM, embedState, embedKont] using
    loop_embed fuel σ (.eval p ρ .halt)

/-- Corollary through quotation. -/
theorem eval_quote_embed (fuel : Nat) (σ : Store)
    (ρ : FactorizationCtrl.Env) (p : FactorizationCtrl.Prog) :
    evalD fuel (embedEnv ρ) σ (quoteD (embed p)) =
      (FactorizationCtrl.runM fuel ρ p).map embedVal := by
  rw [eval_quote, runM_embed]

/-- Ω's divergence transfers for free through the bisimulation. -/
theorem Omega_still_diverges (fuel : Nat) (σ : Store)
    (ρ : FactorizationCtrl.Env) :
    runM fuel (embedEnv ρ) σ (embed FactorizationCtrl.OmegaM) = none := by
  simp [runM_embed, FactorizationCtrl.machine_Omega_diverges]

end FactorizationStore
end Dichotomic

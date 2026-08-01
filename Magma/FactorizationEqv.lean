import Magma.FactorizationData

/-!
# Factorization with Identity: the `eqv?` Core Form

The second breadth rung, and the one item of the R7RS roadmap that is
Lean-first by necessity (`kamea-machine` README: "an `eqv?` core form
(Lean-first — unlocks true `null?` and faster element comparison)").
The machine gains **atomic identity**: a binary form `eqv` deciding
identity of the machine's two kinds of atoms —

* **table elements**, by index — and by the artifact's extensionality
  this is *observational* equality: two instructions are
  `eqv?`-identical iff their rows in the certified table coincide
  (`eqv_elem_observational`). The primitive adds speed, not power: a
  decision tree of applications could already observe this (the
  metacircular evaluator's tag dispatch does exactly that);
* **store locations**, by index — R7RS's "same location" semantics,
  previously unobservable (locations were opaque). Two allocations are
  distinct (`eqv_fresh_refs`); a location is identical to itself
  (`eqv_same_ref`).

Compound and runtime values are **never** `eqv?`-identical
(`eqv_cell_never`): cells here are immutable tape *values*, not
locations, so R7RS's location-based pair identity has no referent —
structural comparison on immutable data is `equal?`'s job (a surface
derivation by `car`/`cdr`/`pairp` recursion), and identity-carrying
mutable structure is exactly what `ref` cells provide. Closures and
continuations compare `ff`, which R7RS permits. The one deviation this
buys, stated honestly: `(eqv? x x)` on a pair is `ff` — the honest
reading of pairs-as-values.

`null?` becomes definable at last: `nullp e := eqv e (atom 0)` — `tt`
exactly on the accept absorber (`nullp_nil`, `nullp_pair`, `nullp_ff`).

The factorization theorem is unchanged once more (14 syntax classes):
`evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p`, uniformly in fuel, base
case still `eatom_qatom`. Certified homoiconicity is carried forward
(`programs_build_their_own_quotations`). Conservativity over the data
rung is again a lockstep bisimulation (`step_embed` → `runM_embed`).

Tag: `eqv` shares shift? (element 7) with the data forms, sub-tagged
7 — identity is the recognizer's last question. With this rung the
sub-tag space {2..7} under shift? is exactly exhausted, matching the
top-level tag space.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationEqv

open Factorization (qatom eatom eatom_qatom)

/-- Programs: the data rung's forms plus atomic identity. -/
inductive Prog where
  | atom   : Fin 8 → Prog
  | var    : Nat → Prog
  | lam    : Prog → Prog
  | app    : Prog → Prog → Prog
  | callcc : Prog → Prog
  | ref    : Prog → Prog
  | deref  : Prog → Prog
  | setref : Prog → Prog → Prog
  | cons   : Prog → Prog → Prog
  | car    : Prog → Prog
  | cdr    : Prog → Prog
  | pairp  : Prog → Prog
  | ite    : Prog → Prog → Prog → Prog
  | eqv    : Prog → Prog → Prog
deriving DecidableEq

mutual
  /-- Tape values (unchanged: identity is a question, not a
      constructor). -/
  inductive Val where
    | elem : Fin 8 → Val
    | cell : Val → Val → Val
    | clos : Prog → List Val → Val
    | cont : Kont → Val
    | loc  : Nat → Val

  /-- Continuations: the data rung's frames plus the two `eqv`
      frames. -/
  inductive Kont where
    | halt   : Kont
    | appL   : Prog → List Val → Kont → Kont
    | appR   : Val → Kont → Kont
    | refK   : Kont → Kont
    | derefK : Kont → Kont
    | setL   : Prog → List Val → Kont → Kont
    | setR   : Val → Kont → Kont
    | consL  : Prog → List Val → Kont → Kont
    | consR  : Val → Kont → Kont
    | carK   : Kont → Kont
    | cdrK   : Kont → Kont
    | pairK  : Kont → Kont
    | iteK   : Prog → Prog → List Val → Kont → Kont
    | eqvL   : Prog → List Val → Kont → Kont
    | eqvR   : Val → Kont → Kont
end

/-- Environments: captured by closures. -/
abbrev Env := List Val

/-- The store: threaded, captured by nothing. -/
abbrev Store := List Val

/-- Atomic identity: elements by table index, locations by store
    index; compound and runtime values are never `eqv?`-identical. -/
def eqvVal : Val → Val → Val
  | .elem a, .elem b => if a = b then .elem 0 else .elem 1
  | .loc n, .loc m => if n = m then .elem 0 else .elem 1
  | _, _ => .elem 1

/-- Machine states: commands ⟨focus ‖ store ‖ continuation⟩. -/
inductive State where
  | eval : Prog → Env → Store → Kont → State
  | ret  : Val → Store → Kont → State

/-- One machine step. -/
def step : State → State ⊕ Val
  | .eval (.atom a) _ σ k => .inl (.ret (.elem a) σ k)
  | .eval (.var n) ρ σ k => .inl (.ret (ρ.getD n (.elem 0)) σ k)
  | .eval (.lam b) ρ σ k => .inl (.ret (.clos b ρ) σ k)
  | .eval (.app f x) ρ σ k => .inl (.eval f ρ σ (.appL x ρ k))
  | .eval (.callcc b) ρ σ k => .inl (.eval b (.cont k :: ρ) σ k)
  | .eval (.ref e) ρ σ k => .inl (.eval e ρ σ (.refK k))
  | .eval (.deref e) ρ σ k => .inl (.eval e ρ σ (.derefK k))
  | .eval (.setref l e) ρ σ k => .inl (.eval l ρ σ (.setL e ρ k))
  | .eval (.cons a b) ρ σ k => .inl (.eval a ρ σ (.consL b ρ k))
  | .eval (.car e) ρ σ k => .inl (.eval e ρ σ (.carK k))
  | .eval (.cdr e) ρ σ k => .inl (.eval e ρ σ (.cdrK k))
  | .eval (.pairp e) ρ σ k => .inl (.eval e ρ σ (.pairK k))
  | .eval (.ite c t e) ρ σ k => .inl (.eval c ρ σ (.iteK t e ρ k))
  | .eval (.eqv a b) ρ σ k => .inl (.eval a ρ σ (.eqvL b ρ k))
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
  | .ret v σ (.consL b ρ k) => .inl (.eval b ρ σ (.consR v k))
  | .ret w σ (.consR v k) => .inl (.ret (.cell v w) σ k)
  | .ret (.cell u _) σ (.carK k) => .inl (.ret u σ k)
  | .ret _ σ (.carK k) => .inl (.ret (.elem 0) σ k)
  | .ret (.cell _ w) σ (.cdrK k) => .inl (.ret w σ k)
  | .ret _ σ (.cdrK k) => .inl (.ret (.elem 0) σ k)
  | .ret (.cell _ _) σ (.pairK k) => .inl (.ret (.elem 0) σ k)
  | .ret _ σ (.pairK k) => .inl (.ret (.elem 1) σ k)
  | .ret (.elem b) σ (.iteK t e ρ k) =>
    .inl (.eval (if b = 1 then e else t) ρ σ k)
  | .ret _ σ (.iteK t _ ρ k) => .inl (.eval t ρ σ k)
  | .ret v σ (.eqvL b ρ k) => .inl (.eval b ρ σ (.eqvR v k))
  | .ret w σ (.eqvR v k) => .inl (.ret (eqvVal v w) σ k)

/-- The comparison is one machine rule: return the identity verdict of
    the two evaluated operands. -/
theorem step_eqv (v w : Val) (σ : Store) (k : Kont) :
    step (.ret w σ (.eqvR v k)) = .inl (.ret (eqvVal v w) σ k) := rfl

/-- Cells are values, not locations: never `eqv?`-identical. -/
theorem eqv_cell_never (u v u' v' : Val) :
    eqvVal (.cell u v) (.cell u' v') = .elem 1 := rfl

/-- The artifact's extensionality, at the table: row equality is index
    equality — checked against all 64 cells by `decide`. -/
theorem dotA8_ext (a b : Fin 8) (h : ∀ c, dotA8 a c = dotA8 b c) :
    a = b := by
  revert a b; decide

/-- **`eqv?` on elements is observational equality**: two instructions
    are identical iff their rows in the certified table coincide — the
    artifact's extensionality law internalized as the correctness of
    the new primitive. The form adds speed, not discriminating power. -/
theorem eqv_elem_observational (a b : Fin 8) :
    eqvVal (.elem a) (.elem b) = .elem 0 ↔ ∀ c, dotA8 a c = dotA8 b c := by
  constructor
  · intro h c
    by_cases hab : a = b
    · rw [hab]
    · exfalso
      have h1 : eqvVal (.elem a) (.elem b) = .elem 1 := by
        simp [eqvVal, hab]
      rw [h] at h1
      injection h1 with h2
      exact absurd h2 (by decide)
  · intro h
    have hab : a = b := dotA8_ext a b h
    simp [eqvVal, hab]

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

/-- Driver-level quote. Tags as at the data rung, plus `eqv`
    sub-tagged 7 under shift? — the last free sub-tag. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .var n => .cell (.elem 4) (natToVal n)
  | .lam b => .cell (.elem 2) (quoteD b)
  | .app f x => .cell (.elem 3) (.cell (quoteD f) (quoteD x))
  | .callcc b => .cell (.elem 6) (quoteD b)
  | .ref e => .cell (.elem 5) (.cell (.elem 2) (quoteD e))
  | .deref e => .cell (.elem 5) (.cell (.elem 3) (quoteD e))
  | .setref l e => .cell (.elem 5) (.cell (.elem 4) (.cell (quoteD l) (quoteD e)))
  | .cons a b => .cell (.elem 7) (.cell (.elem 2) (.cell (quoteD a) (quoteD b)))
  | .car e => .cell (.elem 7) (.cell (.elem 3) (quoteD e))
  | .cdr e => .cell (.elem 7) (.cell (.elem 4) (quoteD e))
  | .pairp e => .cell (.elem 7) (.cell (.elem 5) (quoteD e))
  | .ite c t e =>
    .cell (.elem 7) (.cell (.elem 6) (.cell (quoteD c) (.cell (quoteD t) (quoteD e))))
  | .eqv a b => .cell (.elem 7) (.cell (.elem 7) (.cell (quoteD a) (quoteD b)))

mutual
  /-- Driver-level decode. Closures, continuations, locations: never
      data. -/
  def decodeD : Val → Option Prog
    | .elem b => some (.atom (eatom b))
    | .cell (.elem h) rest =>
      if h = (2 : Fin 8) then (decodeD rest).map .lam
      else if h = (3 : Fin 8) then decodeApp rest
      else if h = (4 : Fin 8) then (valToNat rest).map .var
      else if h = (5 : Fin 8) then decodeStore rest
      else if h = (6 : Fin 8) then (decodeD rest).map .callcc
      else if h = (7 : Fin 8) then decodeData rest
      else none
    | _ => none

  def decodeApp : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some f, some x => some (.app f x)
      | _, _ => none
    | _ => none

  def decodeStore : Val → Option Prog
    | .cell (.elem d) rest =>
      if d = (2 : Fin 8) then (decodeD rest).map .ref
      else if d = (3 : Fin 8) then (decodeD rest).map .deref
      else if d = (4 : Fin 8) then decodeSet rest
      else none
    | _ => none

  def decodeSet : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some l, some e => some (.setref l e)
      | _, _ => none
    | _ => none

  def decodeData : Val → Option Prog
    | .cell (.elem d) rest =>
      if d = (2 : Fin 8) then decodePair rest
      else if d = (3 : Fin 8) then (decodeD rest).map .car
      else if d = (4 : Fin 8) then (decodeD rest).map .cdr
      else if d = (5 : Fin 8) then (decodeD rest).map .pairp
      else if d = (6 : Fin 8) then decodeIte rest
      else if d = (7 : Fin 8) then decodeEqv rest
      else none
    | _ => none

  def decodePair : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some a, some b => some (.cons a b)
      | _, _ => none
    | _ => none

  def decodeIte : Val → Option Prog
    | .cell c (.cell t e) =>
      match decodeD c, decodeD t, decodeD e with
      | some pc, some pt, some pe => some (.ite pc pt pe)
      | _, _, _ => none
    | _ => none

  def decodeEqv : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some a, some b => some (.eqv a b)
      | _, _ => none
    | _ => none
end

/-- User-level eval. -/
def evalD (fuel : Nat) (ρ : Env) (σ : Store) (v : Val) : Option Val :=
  match decodeD v with
  | some p => runM fuel ρ σ p
  | none => some (.elem 0)

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, still static** across all 14 syntax
    classes. Base case: the certified table law `eatom_qatom`. -/
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
  | cons a b iha ihb =>
    simp [quoteD, decodeD, decodeData, decodePair, iha, ihb]
  | car e ih => simp [quoteD, decodeD, decodeData, ih]
  | cdr e ih => simp [quoteD, decodeD, decodeData, ih]
  | pairp e ih => simp [quoteD, decodeD, decodeData, ih]
  | ite c t e ihc iht ihe =>
    simp [quoteD, decodeD, decodeData, decodeIte, ihc, iht, ihe]
  | eqv a b iha ihb =>
    simp [quoteD, decodeD, decodeData, decodeEqv, iha, ihb]

/-- **The factorization theorem with identity**: uniformly in fuel,
    `eval fuel ρ σ (quote p) = runM fuel ρ σ p`. -/
theorem eval_quote (fuel : Nat) (ρ : Env) (σ : Store) (p : Prog) :
    evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p := by
  simp [evalD, decode_quote]

-- ------------------------------------------------------------------
-- null? and the identity demos.
-- ------------------------------------------------------------------

/-- `null?`, at last: identity with the accept absorber. -/
def nullp (e : Prog) : Prog := .eqv e (.atom 0)

/-- `(null? '())` is true: nil is the accept absorber. -/
theorem nullp_nil (ρ : Env) (σ : Store) :
    runM 8 ρ σ (nullp (.atom 0)) = some (.elem 0) := rfl

/-- `(null? (cons a b))` is false — the discrimination `pairp` alone
    could not make against `tt`. -/
theorem nullp_pair (ρ : Env) (σ : Store) :
    runM 12 ρ σ (nullp (.cons (.atom 2) (.atom 3))) = some (.elem 1) := rfl

/-- `(null? ff)` is false: element identity, not truthiness. -/
theorem nullp_ff (ρ : Env) (σ : Store) :
    runM 8 ρ σ (nullp (.atom 1)) = some (.elem 1) := rfl

/-- Two allocations are distinct locations — `eqv?` observes store
    identity, which was previously opaque. -/
theorem eqv_fresh_refs (ρ : Env) :
    runM 16 ρ [] (.eqv (.ref (.atom 2)) (.ref (.atom 2))) =
      some (.elem 1) := rfl

/-- A location is identical to itself — R7RS's "same location",
    reached through β so the two operands are one binding. -/
theorem eqv_same_ref (ρ : Env) :
    runM 16 ρ [] (.app (.lam (.eqv (.var 0) (.var 0))) (.ref (.atom 2))) =
      some (.elem 0) := rfl

-- ------------------------------------------------------------------
-- Certified homoiconicity: carried to the identity rung.
-- ------------------------------------------------------------------

/-- The constructor program of a data-only value: atoms for elements,
    `cons` for cells; runtime-only values have no constructor. -/
def build : Val → Option Prog
  | .elem a => some (.atom a)
  | .cell u v =>
    match build u, build v with
    | some pu, some pv => some (.cons pu pv)
    | _, _ => none
  | _ => none

local macro "build_impossible" : tactic =>
  `(tactic|
    (intro v hb ρ σ k n w hn
     exfalso
     cases v with
     | elem b => simp [build] at hb
     | cell u u' =>
       cases hu : build u <;> cases hu' : build u' <;>
         simp [build, hu, hu'] at hb
     | clos b' ρ' => simp [build] at hb
     | cont k' => simp [build] at hb
     | loc l => simp [build] at hb))

/-- **The constructor computes its value**, continuation-polymorphically:
    if returning v to k eventually answers w, then running v's
    constructor program in k eventually answers w. -/
theorem build_sim :
    ∀ (p : Prog) {v : Val}, build v = some p →
      ∀ (ρ : Env) (σ : Store) (k : Kont) (n : Nat) (w : Val),
        loop n (.ret v σ k) = some w →
        ∃ m, loop m (.eval p ρ σ k) = some w := by
  intro p
  induction p with
  | atom a =>
    intro v hb ρ σ k n w hn
    cases v with
    | elem b =>
      simp [build] at hb
      subst hb
      exact ⟨n + 1, hn⟩
    | cell u u' =>
      exfalso
      cases hu : build u <;> cases hu' : build u' <;>
        simp [build, hu, hu'] at hb
    | clos b' ρ' => simp [build] at hb
    | cont k' => simp [build] at hb
    | loc l => simp [build] at hb
  | cons pu pv ihu ihv =>
    intro v hb ρ σ k n w hn
    cases v with
    | elem b => simp [build] at hb
    | cell u u' =>
      simp only [build] at hb
      cases hu : build u with
      | none => rw [hu] at hb; simp at hb
      | some qu =>
        rw [hu] at hb
        cases hu' : build u' with
        | none => rw [hu'] at hb; simp at hb
        | some qv =>
          rw [hu'] at hb
          simp at hb
          obtain ⟨rfl, rfl⟩ := hb
          have h2 : loop (n + 1) (.ret u' σ (.consR u k)) = some w := by
            simp only [loop, step]
            exact hn
          obtain ⟨m2, hm2⟩ := ihv hu' ρ σ (.consR u k) (n + 1) w h2
          have h1 : loop (m2 + 1) (.ret u σ (.consL qv ρ k)) = some w := by
            simp only [loop, step]
            exact hm2
          obtain ⟨m1, hm1⟩ := ihu hu ρ σ (.consL qv ρ k) (m2 + 1) w h1
          refine ⟨m1 + 1, ?_⟩
          simp only [loop, step]
          exact hm1
    | clos b' ρ' => simp [build] at hb
    | cont k' => simp [build] at hb
    | loc l => simp [build] at hb
  | var i => build_impossible
  | lam b ih => build_impossible
  | app f x ihf ihx => build_impossible
  | callcc b ih => build_impossible
  | ref e ih => build_impossible
  | deref e ih => build_impossible
  | setref l e ihl ihe => build_impossible
  | car e ih => build_impossible
  | cdr e ih => build_impossible
  | pairp e ih => build_impossible
  | ite c t e ihc iht ihe => build_impossible
  | eqv a b iha ihb => build_impossible

theorem build_natToVal : ∀ n : Nat, ∃ p, build (natToVal n) = some p := by
  intro n
  induction n with
  | zero => exact ⟨_, rfl⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 4) p, by simp [natToVal, build, hp]⟩

/-- Every quotation is data-only, hence constructible. -/
theorem build_quote : ∀ q : Prog, ∃ p, build (quoteD q) = some p := by
  intro q
  induction q with
  | atom a => exact ⟨_, rfl⟩
  | var n =>
    obtain ⟨p, hp⟩ := build_natToVal n
    exact ⟨.cons (.atom 4) p, by simp [quoteD, build, hp]⟩
  | lam b ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 2) p, by simp [quoteD, build, hp]⟩
  | app f x ihf ihx =>
    obtain ⟨pf, hf⟩ := ihf
    obtain ⟨px, hx⟩ := ihx
    exact ⟨.cons (.atom 3) (.cons pf px), by simp [quoteD, build, hf, hx]⟩
  | callcc b ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 6) p, by simp [quoteD, build, hp]⟩
  | ref e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 5) (.cons (.atom 2) p), by simp [quoteD, build, hp]⟩
  | deref e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 5) (.cons (.atom 3) p), by simp [quoteD, build, hp]⟩
  | setref l e ihl ihe =>
    obtain ⟨pl, hl⟩ := ihl
    obtain ⟨pe, he⟩ := ihe
    exact ⟨.cons (.atom 5) (.cons (.atom 4) (.cons pl pe)),
      by simp [quoteD, build, hl, he]⟩
  | cons a b iha ihb =>
    obtain ⟨pa, ha⟩ := iha
    obtain ⟨pb, hb⟩ := ihb
    exact ⟨.cons (.atom 7) (.cons (.atom 2) (.cons pa pb)),
      by simp [quoteD, build, ha, hb]⟩
  | car e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 7) (.cons (.atom 3) p), by simp [quoteD, build, hp]⟩
  | cdr e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 7) (.cons (.atom 4) p), by simp [quoteD, build, hp]⟩
  | pairp e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.atom 7) (.cons (.atom 5) p), by simp [quoteD, build, hp]⟩
  | ite c t e ihc iht ihe =>
    obtain ⟨pc, hc⟩ := ihc
    obtain ⟨pt, ht⟩ := iht
    obtain ⟨pe, he⟩ := ihe
    exact ⟨.cons (.atom 7) (.cons (.atom 6) (.cons pc (.cons pt pe))),
      by simp [quoteD, build, hc, ht, he]⟩
  | eqv a b iha ihb =>
    obtain ⟨pa, ha⟩ := iha
    obtain ⟨pb, hb⟩ := ihb
    exact ⟨.cons (.atom 7) (.cons (.atom 7) (.cons pa pb)),
      by simp [quoteD, build, ha, hb]⟩

/-- **Certified homoiconicity**, carried: for every program q there is
    a program that computes q's quotation — `eqv` programs included. -/
theorem programs_build_their_own_quotations
    (q : Prog) (ρ : Env) (σ : Store) :
    ∃ (p : Prog) (fuel : Nat), runM fuel ρ σ p = some (quoteD q) := by
  obtain ⟨p, hp⟩ := build_quote q
  obtain ⟨m, hm⟩ :=
    build_sim p hp ρ σ .halt 1 (quoteD q) rfl
  exact ⟨p, m, hm⟩

-- ------------------------------------------------------------------
-- Conservativity over the data rung: lockstep bisimulation.
-- ------------------------------------------------------------------

/-- The data rung embeds: its programs are the identity-free ones. -/
def embed : FactorizationData.Prog → Prog
  | .atom a => .atom a
  | .var n => .var n
  | .lam b => .lam (embed b)
  | .app f x => .app (embed f) (embed x)
  | .callcc b => .callcc (embed b)
  | .ref e => .ref (embed e)
  | .deref e => .deref (embed e)
  | .setref l e => .setref (embed l) (embed e)
  | .cons a b => .cons (embed a) (embed b)
  | .car e => .car (embed e)
  | .cdr e => .cdr (embed e)
  | .pairp e => .pairp (embed e)
  | .ite c t e => .ite (embed c) (embed t) (embed e)

mutual
  def embedVal : FactorizationData.Val → Val
    | .elem a => .elem a
    | .cell u v => .cell (embedVal u) (embedVal v)
    | .clos b ρ => .clos (embed b) (embedEnv ρ)
    | .cont k => .cont (embedKont k)
    | .loc n => .loc n

  def embedEnv : List FactorizationData.Val → List Val
    | [] => []
    | v :: ρ => embedVal v :: embedEnv ρ

  def embedKont : FactorizationData.Kont → Kont
    | .halt => .halt
    | .appL x ρ k => .appL (embed x) (embedEnv ρ) (embedKont k)
    | .appR v k => .appR (embedVal v) (embedKont k)
    | .refK k => .refK (embedKont k)
    | .derefK k => .derefK (embedKont k)
    | .setL e ρ k => .setL (embed e) (embedEnv ρ) (embedKont k)
    | .setR v k => .setR (embedVal v) (embedKont k)
    | .consL b ρ k => .consL (embed b) (embedEnv ρ) (embedKont k)
    | .consR v k => .consR (embedVal v) (embedKont k)
    | .carK k => .carK (embedKont k)
    | .cdrK k => .cdrK (embedKont k)
    | .pairK k => .pairK (embedKont k)
    | .iteK t e ρ k => .iteK (embed t) (embed e) (embedEnv ρ) (embedKont k)
end

/-- A data-rung state, embedded (store embedded pointwise). -/
def embedState : FactorizationData.State → State
  | .eval p ρ σ k => .eval (embed p) (embedEnv ρ) (embedEnv σ) (embedKont k)
  | .ret v σ k => .ret (embedVal v) (embedEnv σ) (embedKont k)

theorem getD_embedEnv (ρ : FactorizationData.Env) (n : Nat) :
    (embedEnv ρ)[n]?.getD (Val.elem 0) =
      embedVal (ρ[n]?.getD (.elem 0)) := by
  induction ρ generalizing n with
  | nil => simp [embedEnv, embedVal]
  | cons u ρ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simpa [embedEnv] using ih m

theorem length_embedEnv (σ : FactorizationData.Store) :
    (embedEnv σ).length = σ.length := by
  induction σ with
  | nil => rfl
  | cons v σ ih => simp [embedEnv, ih]

theorem append_embedEnv (σ : FactorizationData.Store)
    (v : FactorizationData.Val) :
    embedEnv (σ ++ [v]) = embedEnv σ ++ [embedVal v] := by
  induction σ with
  | nil => rfl
  | cons u σ ih => simp [embedEnv, ih]

theorem set_embedEnv (σ : FactorizationData.Store) (n : Nat)
    (v : FactorizationData.Val) :
    embedEnv (σ.set n v) = (embedEnv σ).set n (embedVal v) := by
  induction σ generalizing n with
  | nil => rfl
  | cons u σ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simp [embedEnv, ih]

set_option linter.unusedSimpArgs false in
/-- **Lockstep bisimulation**: on identity-free programs the machine
    performs exactly the data rung's step. -/
theorem step_embed (s : FactorizationData.State) :
    step (embedState s) =
      (FactorizationData.step s).map embedState embedVal := by
  cases s with
  | eval p ρ σ k =>
    cases p <;>
      simp [embedState, embed, embedVal, embedEnv, embedKont, step,
        FactorizationData.step, getD_embedEnv]
  | ret v σ k =>
    cases k with
    | halt => simp [embedState, embedKont, step, FactorizationData.step]
    | appL x ρ k =>
      simp [embedState, embedKont, step, FactorizationData.step]
    | appR u k =>
      cases u <;> cases v <;>
        simp [embedState, embed, embedVal, embedEnv, embedKont, step,
          FactorizationData.step]
    | refK k =>
      simp [embedState, embedVal, embedKont, step, FactorizationData.step,
        length_embedEnv, append_embedEnv]
    | derefK k =>
      cases v <;>
        simp [embedState, embedVal, embedKont, step,
          FactorizationData.step, getD_embedEnv]
    | setL e ρ k =>
      simp [embedState, embedKont, step, FactorizationData.step]
    | setR u k =>
      cases u <;>
        simp [embedState, embedVal, embedKont, step,
          FactorizationData.step, set_embedEnv]
    | consL b ρ k =>
      simp [embedState, embedKont, step, FactorizationData.step]
    | consR u k =>
      simp [embedState, embedVal, embedKont, step, FactorizationData.step]
    | carK k =>
      cases v <;>
        simp [embedState, embedVal, embedKont, step, FactorizationData.step]
    | cdrK k =>
      cases v <;>
        simp [embedState, embedVal, embedKont, step, FactorizationData.step]
    | pairK k =>
      cases v <;>
        simp [embedState, embedVal, embedKont, step, FactorizationData.step]
    | iteK t e ρ k =>
      cases v <;>
        simp [embedState, embed, embedVal, embedEnv, embedKont, step,
          FactorizationData.step, apply_ite]

theorem loop_embed (n : Nat) (s : FactorizationData.State) :
    loop n (embedState s) = (FactorizationData.loop n s).map embedVal := by
  induction n generalizing s with
  | zero => rfl
  | succ m ih =>
    simp only [loop, FactorizationData.loop, step_embed]
    cases FactorizationData.step s with
    | inl s' => simpa using ih s'
    | inr v => rfl

/-- **Conservativity**: on identity-free programs the machine's answer
    is exactly the data rung's — value or divergence alike. -/
theorem runM_embed (fuel : Nat) (ρ : FactorizationData.Env)
    (σ : FactorizationData.Store) (p : FactorizationData.Prog) :
    runM fuel (embedEnv ρ) (embedEnv σ) (embed p) =
      (FactorizationData.runM fuel ρ σ p).map embedVal := by
  simpa [runM, FactorizationData.runM, embedState, embedKont] using
    loop_embed fuel (.eval p ρ σ .halt)

end FactorizationEqv
end Dichotomic

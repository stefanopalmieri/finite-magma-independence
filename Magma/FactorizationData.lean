import Magma.FactorizationStore

/-!
# Factorization with Data: Pairs on the Tape, and Certified Homoiconicity

The first breadth rung (Phase 3 of the Rust host's roadmap): the
machine gains **structured data and dispatch** — `cons`/`car`/`cdr`,
the recognizer `pairp`, and the conditional `ite`. Everything lands
exactly where the walls said it must:

* `cons` builds **tape cells** — the pairing wall forbids faithful
  internal pairing, so pairs are heap values, not table elements;
* `pairp` reads **heap structure** — the recognizer wall forbids a
  non-trivial internal recognizer of a faithful constructor, so
  `pair?` inspects the value's constructor, never instruction
  identity;
* `ite` is a **machine form** — the Branch enrichment was removed from
  the table (branching is not a table capability); dispatch on a value
  is driver/machine work. Truthiness is R7RS-shaped: the reject
  absorber (element 1) is the only false value.

The headline is **certified homoiconicity**. Quotations are cells, and
`cons` builds cells — so programs can now construct quotations:

* `build v` — the program that constructs a data-only value v
  (`build_sim`: it computes v, continuation-polymorphically);
* `build_quote` — every quotation is data-only, hence constructible;
* `programs_build_their_own_quotations` — for **every** program q
  there is a program that computes `quoteD q`; composed with
  `eval_quote`, eval of the built quotation runs q. Code as data,
  data as code, both directions theorems.

The factorization theorem is unchanged once more (13 syntax classes
now): `evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p`, uniformly in
fuel, base case still `eatom_qatom`. Conservativity over the store
rung is again a lockstep bisimulation (`step_embed` → `runM_embed`).

Tags: the data forms share shift? (element 7) — the last free element
— sub-tagged 2 = `cons`, 3 = `car`, 4 = `cdr`, 5 = `pairp` (the
recognizer's sub-tag is data? — fitting), 6 = `ite` (dispatch tagged
by the judge). Tag values are engineering (`MACHINE.md` §8); the
necessity of tags is not. With this rung the tag space {2..7} is
exactly exhausted.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationData

open Factorization (qatom eatom eatom_qatom)

/-- Programs: the store rung's forms plus pairs and dispatch. -/
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
deriving DecidableEq

mutual
  /-- Tape values (unchanged: `cons` builds cells, no new
      constructor). -/
  inductive Val where
    | elem : Fin 8 → Val
    | cell : Val → Val → Val
    | clos : Prog → List Val → Val
    | cont : Kont → Val
    | loc  : Nat → Val

  /-- Continuations: the store rung's frames plus pair and dispatch
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
end

/-- Environments: captured by closures. -/
abbrev Env := List Val

/-- The store: threaded, captured by nothing. -/
abbrev Store := List Val

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

/-- `cons` builds a tape cell — pairs live on the heap, per the
    pairing wall. -/
theorem step_cons (w v : Val) (σ : Store) (k : Kont) :
    step (.ret w σ (.consR v k)) = .inl (.ret (.cell v w) σ k) := rfl

/-- `pair?` reads heap structure, never instruction identity — the
    recognizer wall's discipline as a machine rule. -/
theorem step_pairp_cell (u w : Val) (σ : Store) (k : Kont) :
    step (.ret (.cell u w) σ (.pairK k)) = .inl (.ret (.elem 0) σ k) := rfl

theorem step_pairp_elem (a : Fin 8) (σ : Store) (k : Kont) :
    step (.ret (.elem a) σ (.pairK k)) = .inl (.ret (.elem 1) σ k) := rfl

/-- Dispatch: the reject absorber is the only false value. -/
theorem step_ite_false (t e : Prog) (ρ : Env) (σ : Store) (k : Kont) :
    step (.ret (.elem 1) σ (.iteK t e ρ k)) = .inl (.eval e ρ σ k) := rfl

theorem step_ite_true (t e : Prog) (ρ : Env) (σ : Store) (k : Kont) :
    step (.ret (.elem 0) σ (.iteK t e ρ k)) = .inl (.eval t ρ σ k) := rfl

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

/-- Driver-level quote. Tags: quote (2) λ, eval (3) app, shift (4)
    var, data? (5) store forms, judge? (6) μ, shift? (7) data forms —
    sub-tagged 2 cons / 3 car / 4 cdr / 5 pairp / 6 ite. The tag space
    {2..7} is now exactly exhausted. -/
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
end

/-- User-level eval. -/
def evalD (fuel : Nat) (ρ : Env) (σ : Store) (v : Val) : Option Val :=
  match decodeD v with
  | some p => runM fuel ρ σ p
  | none => some (.elem 0)

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, still static** across all 13 syntax
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

/-- **The factorization theorem with data**: uniformly in fuel,
    `eval fuel ρ σ (quote p) = runM fuel ρ σ p`. -/
theorem eval_quote (fuel : Nat) (ρ : Env) (σ : Store) (p : Prog) :
    evalD fuel ρ σ (quoteD p) = runM fuel ρ σ p := by
  simp [evalD, decode_quote]

-- ------------------------------------------------------------------
-- Certified homoiconicity: programs build quotations.
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
    constructor program in k eventually answers w. The store threads
    untouched — `cons` builds immediate cells, it does not allocate. -/
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

/-- **Certified homoiconicity**: for every program q there is a
    program that computes q's quotation — in any environment, with any
    store (which it leaves untouched). Composed with `eval_quote`,
    eval of the built quotation runs q: code as data and data as code,
    both directions theorems. -/
theorem programs_build_their_own_quotations
    (q : Prog) (ρ : Env) (σ : Store) :
    ∃ (p : Prog) (fuel : Nat), runM fuel ρ σ p = some (quoteD q) := by
  obtain ⟨p, hp⟩ := build_quote q
  obtain ⟨m, hm⟩ :=
    build_sim p hp ρ σ .halt 1 (quoteD q) rfl
  exact ⟨p, m, hm⟩

/-- The concrete loop, end to end: `(cons evl-code (cons quo-code
    eval-code))` builds exactly the quotation of `(quo evl)`, and eval
    of that cell is running `(quo evl)`. -/
theorem constructed_quotation_demo (ρ : Env) (σ : Store) :
    runM 12 ρ σ (.cons (.atom 3) (.cons (.atom 5) (.atom 6))) =
      some (quoteD (.app (.atom 2) (.atom 3))) := rfl

theorem eval_of_constructed_demo (fuel : Nat) (ρ : Env) (σ : Store) :
    evalD fuel ρ σ (.cell (.elem 3) (.cell (.elem 5) (.elem 6))) =
      runM fuel ρ σ (.app (.atom 2) (.atom 3)) :=
  eval_quote fuel ρ σ (.app (.atom 2) (.atom 3))

/-- Pairs work: car ∘ cons, and the recognizer on both sides. -/
theorem car_cons_demo (ρ : Env) (σ : Store) :
    runM 8 ρ σ (.car (.cons (.atom 2) (.atom 3))) = some (.elem 2) := rfl

theorem pairp_demo (ρ : Env) (σ : Store) :
    runM 8 ρ σ (.pairp (.cons (.atom 0) (.atom 1))) = some (.elem 0) ∧
      runM 8 ρ σ (.pairp (.atom 4)) = some (.elem 1) :=
  ⟨rfl, rfl⟩

/-- Dispatch demos: ff selects the else-branch; anything else the
    then-branch. -/
theorem ite_demo (ρ : Env) (σ : Store) :
    runM 8 ρ σ (.ite (.atom 1) (.atom 2) (.atom 3)) = some (.elem 3) ∧
      runM 8 ρ σ (.ite (.atom 0) (.atom 2) (.atom 3)) = some (.elem 2) :=
  ⟨rfl, rfl⟩

-- ------------------------------------------------------------------
-- Conservativity over the store rung: lockstep bisimulation.
-- ------------------------------------------------------------------

/-- The store rung embeds: its programs are the data-free ones. -/
def embed : FactorizationStore.Prog → Prog
  | .atom a => .atom a
  | .var n => .var n
  | .lam b => .lam (embed b)
  | .app f x => .app (embed f) (embed x)
  | .callcc b => .callcc (embed b)
  | .ref e => .ref (embed e)
  | .deref e => .deref (embed e)
  | .setref l e => .setref (embed l) (embed e)

mutual
  def embedVal : FactorizationStore.Val → Val
    | .elem a => .elem a
    | .cell u v => .cell (embedVal u) (embedVal v)
    | .clos b ρ => .clos (embed b) (embedEnv ρ)
    | .cont k => .cont (embedKont k)
    | .loc n => .loc n

  def embedEnv : List FactorizationStore.Val → List Val
    | [] => []
    | v :: ρ => embedVal v :: embedEnv ρ

  def embedKont : FactorizationStore.Kont → Kont
    | .halt => .halt
    | .appL x ρ k => .appL (embed x) (embedEnv ρ) (embedKont k)
    | .appR v k => .appR (embedVal v) (embedKont k)
    | .refK k => .refK (embedKont k)
    | .derefK k => .derefK (embedKont k)
    | .setL e ρ k => .setL (embed e) (embedEnv ρ) (embedKont k)
    | .setR v k => .setR (embedVal v) (embedKont k)
end

/-- A store-rung state, embedded (store embedded pointwise). -/
def embedState : FactorizationStore.State → State
  | .eval p ρ σ k => .eval (embed p) (embedEnv ρ) (embedEnv σ) (embedKont k)
  | .ret v σ k => .ret (embedVal v) (embedEnv σ) (embedKont k)

theorem getD_embedEnv (ρ : FactorizationStore.Env) (n : Nat) :
    (embedEnv ρ)[n]?.getD (Val.elem 0) =
      embedVal (ρ[n]?.getD (.elem 0)) := by
  induction ρ generalizing n with
  | nil => simp [embedEnv, embedVal]
  | cons u ρ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simpa [embedEnv] using ih m

theorem length_embedEnv (σ : FactorizationStore.Store) :
    (embedEnv σ).length = σ.length := by
  induction σ with
  | nil => rfl
  | cons v σ ih => simp [embedEnv, ih]

theorem append_embedEnv (σ : FactorizationStore.Store)
    (v : FactorizationStore.Val) :
    embedEnv (σ ++ [v]) = embedEnv σ ++ [embedVal v] := by
  induction σ with
  | nil => rfl
  | cons u σ ih => simp [embedEnv, ih]

theorem set_embedEnv (σ : FactorizationStore.Store) (n : Nat)
    (v : FactorizationStore.Val) :
    embedEnv (σ.set n v) = (embedEnv σ).set n (embedVal v) := by
  induction σ generalizing n with
  | nil => rfl
  | cons u σ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simp [embedEnv, ih]

set_option linter.unusedSimpArgs false in
/-- **Lockstep bisimulation**: on data-free programs the machine
    performs exactly the store rung's step. -/
theorem step_embed (s : FactorizationStore.State) :
    step (embedState s) =
      (FactorizationStore.step s).map embedState embedVal := by
  cases s with
  | eval p ρ σ k =>
    cases p <;>
      simp [embedState, embed, embedVal, embedEnv, embedKont, step,
        FactorizationStore.step, getD_embedEnv]
  | ret v σ k =>
    cases k with
    | halt => simp [embedState, embedKont, step, FactorizationStore.step]
    | appL x ρ k =>
      simp [embedState, embedKont, step, FactorizationStore.step]
    | appR u k =>
      cases u <;> cases v <;>
        simp [embedState, embed, embedVal, embedEnv, embedKont, step,
          FactorizationStore.step]
    | refK k =>
      simp [embedState, embedVal, embedKont, step, FactorizationStore.step,
        length_embedEnv, append_embedEnv]
    | derefK k =>
      cases v <;>
        simp [embedState, embedVal, embedKont, step,
          FactorizationStore.step, getD_embedEnv]
    | setL e ρ k =>
      simp [embedState, embedKont, step, FactorizationStore.step]
    | setR u k =>
      cases u <;>
        simp [embedState, embedVal, embedKont, step,
          FactorizationStore.step, set_embedEnv]

theorem loop_embed (n : Nat) (s : FactorizationStore.State) :
    loop n (embedState s) = (FactorizationStore.loop n s).map embedVal := by
  induction n generalizing s with
  | zero => rfl
  | succ m ih =>
    simp only [loop, FactorizationStore.loop, step_embed]
    cases FactorizationStore.step s with
    | inl s' => simpa using ih s'
    | inr v => rfl

/-- **Conservativity**: on data-free programs the machine's answer is
    exactly the store rung's — value or divergence alike. -/
theorem runM_embed (fuel : Nat) (ρ : FactorizationStore.Env)
    (σ : FactorizationStore.Store) (p : FactorizationStore.Prog) :
    runM fuel (embedEnv ρ) (embedEnv σ) (embed p) =
      (FactorizationStore.runM fuel ρ σ p).map embedVal := by
  simpa [runM, FactorizationStore.runM, embedState, embedKont] using
    loop_embed fuel (.eval p ρ σ .halt)

end FactorizationData
end Dichotomic

import Magma.AdequacyStartup
import Magma.AdequacyInstances
import Magma.AdequacyLeaf

/-!
# Adequacy campaign, rung 3b(iv): the general simulation induction

**Universal adequacy for the applicative fragment.** The theorem the
β families of 3b(iii) were base cases for: `meval_sim` — for *every*
program of the pure fragment (atoms, variables, lambdas,
applications, arbitrarily nested), every represented environment,
and every continuation, META's recursive interpretation simulates
the machine, with the results in the representation relation. The
induction is over a big-step evaluation relation `EvP` mirroring the
machine's five application arms; META's side is glued from a small
kit of *dispatch lemmas*, each a single symbolic kernel reduction.

The architecture, discovered by probe and then certified by `rfl`:

* **The calling convention** (`mevalCall`): META's internal `meval`
  is the knot-cell-9 closure, curried — quotation first, then the
  tagged environment. Every recursive self-call re-enters the same
  state shape: inner body focused, `ρT :: q :: e₉` bound (`e₉` the
  42-entry captured environment), knot store, arbitrary continuation.
  Extracted self-computingly from the store the startup lemma built.
* **Recursive calls are frame-compositional**: evaluating `app f x`,
  META reaches the recursive call for `f` in exactly 129 steps under
  a continuation transformer (`appKf`), reaches the call for `x` 29
  steps after `f`'s value returns (`appKx`), and the apply phase is
  a **tail call**: the closure branch re-enters `mevalCall` for the
  body at the *original* continuation (214 steps), so the induction
  needs no continuation reasoning at all — `KRempty` suffices.
* **The continuation transformers are self-computing projections**:
  `appKf`/`appKx` are defined by running the machine and projecting
  the continuation; the dispatch lemmas' `rfl`s then certify which
  arguments each transformer actually depends on.
* **`mnth` is structurally recursive with the relation** (knot cell
  8, chain then numeral, tail-recursive through its forwarder): the
  nil case never inspects the numeral (10 steps — the leaf rung's
  passenger, now one case of an induction), cons-zero returns the
  head (13), cons-succ re-enters on both tails (31) — exactly the
  three clauses of rung 2's `chainNth`, so `mnth_sim` closes by
  induction on the numeral against the `RepEnv` derivation.
* **The magma lives in the interpreted world**: `mapply` on two
  quoted elements computes the *table product* through the tag trees
  — `mapply_elem_elem` certifies `(quo.a) · (quo.b) ⇓ (quo.a·b)`
  against `dotA8`, all 64 pairs, uniformly in 198 steps.
* **Every error arm agrees** (§5 risk 3 of ADEQUACY.md, discharged
  for this fragment): element-applied-to-non-element, cell-applied,
  loc-applied — META returns `(quo.tt)` exactly where the machine
  returns `elem 0`, and the relation pairs them.

Corollaries: `adequacy_pure` (top-level adequacy for every `EvP`-
convergent closed pure program — the meta run, the direct run, and
the representation, from one derivation), and `adequacy_id_tower` —
adequacy for id-towers of *unbounded nesting depth* over *all*
variable indices: a family infinite in program **structure**, out of
reach of any finite collection of per-skeleton kernel reductions.

Fuel is existential at this rung; the monotone per-form fuel
transformers (and with them divergence transfer) are rung 7's
finishing move. Data, store, and control forms extend `EvP` and the
dispatch kit at rungs 4–6.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacySim

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep AdequacyLeaf

/-! ## Fuel composition -/

/-- Completed segments chain, whatever the tail produces. -/
theorem stepIter_chain {a : Nat} {s s₁ : State}
    (h : stepIter a s = .inl s₁) {b : Nat} {r : State ⊕ Val}
    (h' : stepIter b s₁ = r) : stepIter (a + b) s = r := by
  rw [stepIter_append h]; exact h'

/-! ## The calling convention, self-computing

META's internal `meval` is the closure the startup lemma left in
knot cell 9: curried, quotation then environment. `mevalCall` is the
state at entry to its inner body — the shape every recursive
self-call re-enters. `mnthCall` is the same extraction for `mnth`
(knot cell 8: chain, then numeral). Both are parametric in the
initial environment `ρ₀`, like everything the knot captured. -/

/-- The recursive-call state of META's `meval`: inner body focused,
    environment `ρT :: q :: e₉`, knot store, arbitrary continuation. -/
def mevalCall (ρ₀ : Env) (q ρT : Val) (κ : Kont) : State :=
  match (knotStoreF ρ₀).getD 9 (.elem 0) with
  | .clos (.lam b) e => .eval b (ρT :: q :: e) (knotStoreF ρ₀) κ
  | _ => .ret (.elem 0) [] .halt

/-- The recursive-call state of META's `mnth`: chain, then numeral. -/
def mnthCall (ρ₀ : Env) (ρT num : Val) (κ : Kont) : State :=
  match (knotStoreF ρ₀).getD 8 (.elem 0) with
  | .clos (.lam b) e => .eval b (num :: ρT :: e) (knotStoreF ρ₀) κ
  | _ => .ret (.elem 0) [] .halt

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- The `meval` entry state of the startup rung reaches the
    calling convention in 17 steps: the wrapper `(λq. meval q tt)`
    dereferences the knot and applies — uniformly in the program. -/
theorem call_entry (p : Prog) :
    stepIter 17 (mevalEntry p) =
      .inl (mevalCall [quoteD p] (quoteD p) (.elem 0) .halt) :=
  rfl

/-! ## The direct machine, big-step

`EvP` mirrors the machine's arms for the pure fragment — including
the three error arms and the element product, which *is* the magma.
No continuation arm: under `KRempty` no represented value is a
continuation, so the simulation never meets one. -/

/-- Big-step evaluation for the applicative fragment, matching the
    machine arm for arm (`evp_steps`). -/
inductive EvP : Prog → Env → Val → Prop where
  | atom (a : Fin 8) (ρ : Env) : EvP (.atom a) ρ (.elem a)
  | var (n : Nat) (ρ : Env) : EvP (.var n) ρ (ρ.getD n (.elem 0))
  | lam (b : Prog) (ρ : Env) : EvP (.lam b) ρ (.clos b ρ)
  | appClos {f x b : Prog} {ρ ρ' : Env} {vx v : Val} :
      EvP f ρ (.clos b ρ') → EvP x ρ vx → EvP b (vx :: ρ') v →
      EvP (.app f x) ρ v
  | appElem {f x : Prog} {ρ : Env} {a b : Fin 8} :
      EvP f ρ (.elem a) → EvP x ρ (.elem b) →
      EvP (.app f x) ρ (.elem (dotA8 a b))
  | appElemErr {f x : Prog} {ρ : Env} {a : Fin 8} {w : Val} :
      EvP f ρ (.elem a) → EvP x ρ w → (∀ b : Fin 8, w ≠ .elem b) →
      EvP (.app f x) ρ (.elem 0)
  | appCellErr {f x : Prog} {ρ : Env} {a d w : Val} :
      EvP f ρ (.cell a d) → EvP x ρ w → EvP (.app f x) ρ (.elem 0)
  | appLocErr {f x : Prog} {ρ : Env} {l : Nat} {w : Val} :
      EvP f ρ (.loc l) → EvP x ρ w → EvP (.app f x) ρ (.elem 0)

/-- `EvP` is sound for the machine: a derivation is a terminating
    run, at every store and continuation (the fragment is pure). -/
theorem evp_steps {p : Prog} {ρ : Env} {v : Val} (h : EvP p ρ v) :
    ∀ (σ : Store) (κ : Kont),
      ∃ n, stepIter n (.eval p ρ σ κ) = .inl (.ret v σ κ) := by
  induction h with
  | atom a ρ => exact fun σ κ => ⟨1, rfl⟩
  | var n ρ => exact fun σ κ => ⟨1, rfl⟩
  | lam b ρ => exact fun σ κ => ⟨1, rfl⟩
  | @appClos f x b ρ ρ' vx v _ _ _ ihf ihx ihb =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.clos b ρ') κ)
    obtain ⟨nb, hb⟩ := ihb σ κ
    exact ⟨1 + (nf + (1 + (nx + (1 + nb)))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx (stepIter_chain rfl hb))))⟩
  | @appElem f x ρ a b _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.elem a) κ)
    exact ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx rfl)))⟩
  | @appElemErr f x ρ a w _ _ hw ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.elem a) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @appCellErr f x ρ a d w _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.cell a d) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl
  | @appLocErr f x ρ l w _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.loc l) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl

/-! ## The dispatch kit

One lemma per arm of META's dispatch, each a symbolic kernel
reduction from `mevalCall`. Step counts are probe-discovered and
`rfl`-certified; every value the count does not depend on is left
universally quantified — the passenger principle, now covering
environments, payloads, and continuations at once. -/

/-- Per-atom dispatch step counts (the tag trees route the eight
    elements through three branch groups). -/
def atomSteps : Fin 8 → Nat := fun a =>
  [66, 66, 70, 70, 70, 48, 48, 48].getD a.val 0

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Atoms**: META recomputes `eatom ∘ qatom = id` through the tag
    trees — for every environment, continuation, and initial
    environment. -/
theorem meval_atom (ρ₀ : Env) (a : Fin 8) (ρT : Val) (κ : Kont) :
    stepIter (atomSteps a) (mevalCall ρ₀ (quoteD (.atom a)) ρT κ) =
      .inl (.ret (.cell (.elem 2) (.elem a)) (knotStoreF ρ₀) κ) := by
  fin_cases a <;> rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Lambdas**: closure formation — the body quotation and the
    environment are pure passengers, so one reduction covers every
    lambda over every environment. -/
theorem meval_lam (ρ₀ : Env) (qb ρT : Val) (κ : Kont) :
    stepIter 115 (mevalCall ρ₀ (.cell (.elem 2) qb) ρT κ) =
      .inl (.ret (.cell (.elem 3) (.cell qb ρT)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Variables dispatch to `mnth`** — a tail call: the lookup
    returns straight to the caller's continuation. The numeral and
    the environment are passengers through the dispatch. -/
theorem meval_var_dispatch (ρ₀ : Env) (num ρT : Val) (κ : Kont) :
    stepIter 116 (mevalCall ρ₀ (.cell (.elem 4) num) ρT κ) =
      .inl (mnthCall ρ₀ ρT num κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- `mnth` on the empty environment: the miss default, never
    inspecting the numeral (the leaf rung's passenger, as a case). -/
theorem mnth_nil (ρ₀ : Env) (num : Val) (κ : Kont) :
    stepIter 10 (mnthCall ρ₀ (.elem 0) num κ) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- `mnth` at zero: the chain head, whatever it is. -/
theorem mnth_zero (ρ₀ : Env) (vT ρT' : Val) (κ : Kont) :
    stepIter 13 (mnthCall ρ₀ (.cell vT ρT') (.elem 0) κ) =
      .inl (.ret vT (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- `mnth` at a successor: recurse on both tails — the state
    re-enters the calling convention, at the same continuation. -/
theorem mnth_succ (ρ₀ : Env) (vT ρT' num : Val) (κ : Kont) :
    stepIter 31 (mnthCall ρ₀ (.cell vT ρT') (.cell (.elem 4) num) κ) =
      .inl (mnthCall ρ₀ ρT' num κ) :=
  rfl

/-- **`mnth` simulates `chainNth`**: induction on the numeral
    against the `RepEnv` derivation, the three `rfl` segments as
    cases. With `RepEnv.chainNth`, lookup lands in the relation —
    misses included. -/
theorem mnth_sim (ρ₀ : Env) :
    ∀ (n : Nat) {ρT : Val} {ρ : Env}, RepEnv 14 KRempty ρT ρ →
      ∀ κ : Kont,
      ∃ m, stepIter m (mnthCall ρ₀ ρT (natToVal n) κ) =
        .inl (.ret (chainNth ρT n) (knotStoreF ρ₀) κ) := by
  intro n
  induction n with
  | zero =>
    intro ρT ρ hρ κ
    cases hρ with
    | nil => exact ⟨10, mnth_nil ρ₀ _ κ⟩
    | cons hv hρ' => exact ⟨13, mnth_zero ρ₀ _ _ κ⟩
  | succ n ih =>
    intro ρT ρ hρ κ
    cases hρ with
    | nil => exact ⟨10, mnth_nil ρ₀ _ κ⟩
    | cons hv hρ' =>
      obtain ⟨m, hm⟩ := ih hρ' κ
      exact ⟨31 + m, stepIter_chain (mnth_succ ρ₀ _ _ _ κ) hm⟩

/-! ### Applications

The three-phase protocol, with two self-computing continuation
transformers. `appKf` is the continuation META installs for the
function sub-evaluation; `appKx` the one for the argument. Both are
defined by running the machine and projecting — the `rfl`s below
certify their actual dependencies (the apply phase, in particular,
is a tail call: `κ` comes back out untouched). -/

/-- Continuation projection (for the self-computing transformers). -/
def projK : State ⊕ Val → Kont
  | .inl (.eval _ _ _ k) => k
  | .inl (.ret _ _ k) => k
  | .inr _ => .halt

/-- The continuation of the function sub-evaluation, by extraction. -/
def appKf (ρ₀ : Env) (qf qx ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 129 (mevalCall ρ₀ (.cell (.elem 3) (.cell qf qx)) ρT κ))

/-- The continuation of the argument sub-evaluation, by extraction. -/
def appKx (ρ₀ : Env) (qf qx ρT vfT : Val) (κ : Kont) : Kont :=
  projK (stepIter 29 (.ret vfT (knotStoreF ρ₀) (appKf ρ₀ qf qx ρT κ)))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Application, phase 1**: 129 steps from the application's call
    to the function's recursive call — both subterm quotations and
    the environment ride as passengers. -/
theorem meval_app_f (ρ₀ : Env) (qf qx ρT : Val) (κ : Kont) :
    stepIter 129 (mevalCall ρ₀ (.cell (.elem 3) (.cell qf qx)) ρT κ) =
      .inl (mevalCall ρ₀ qf ρT (appKf ρ₀ qf qx ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Application, phase 2**: 29 steps from the function value's
    return to the argument's recursive call. The function value is
    a passenger — META stores it unexamined until apply time. -/
theorem meval_app_x (ρ₀ : Env) (qf qx ρT vfT : Val) (κ : Kont) :
    stepIter 29 (.ret vfT (knotStoreF ρ₀) (appKf ρ₀ qf qx ρT κ)) =
      .inl (mevalCall ρ₀ qx ρT (appKx ρ₀ qf qx ρT vfT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, closure branch — a tail call**: 214 steps from the
    argument value's return to the body's recursive call, over the
    extended environment, at the *original* continuation. This is
    the lemma that makes the induction go through without touching
    continuations. -/
theorem mapply_clos (ρ₀ : Env) (qf qx ρT qb ρT' vxT : Val) (κ : Kont) :
    stepIter 214 (.ret vxT (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 3) (.cell qb ρT')) κ)) =
      .inl (mevalCall ρ₀ qb (.cell vxT ρT') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, element·element, approach**: 196 steps from the
    argument value's return to the *naked host application* of the
    two elements — every probe on the way tests a tag, never a
    payload, so both elements are passengers and one reduction
    covers the whole 8×8 square. -/
theorem mapply_elem_pre (ρ₀ : Env) (qf qx ρT : Val) (a b : Fin 8)
    (κ : Kont) :
    stepIter 196 (.ret (.cell (.elem 2) (.elem b)) (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.elem b) (knotStoreF ρ₀)
        (.appR (.elem a) (.consR (.elem 2) κ))) :=
  rfl

/-- **The table fires**: the machine's own product arm computes
    `dotA8 a b` — symbolically, at any store — and one `consR` step
    tags the result. META's magma *is* the machine's magma, met in
    a naked application mid-interpretation. -/
theorem elem_fire (σ : Store) (a b : Fin 8) (κ : Kont) :
    stepIter 2 (.ret (.elem b) σ
        (.appR (.elem a) (.consR (.elem 2) κ))) =
      .inl (.ret (.cell (.elem 2) (.elem (dotA8 a b))) σ κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, element·element — the magma through the interpreter**:
    all 64 pairs, one composition, no case split. -/
theorem mapply_elem_elem (ρ₀ : Env) (qf qx ρT : Val) (a b : Fin 8)
    (κ : Kont) :
    stepIter 198 (.ret (.cell (.elem 2) (.elem b)) (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem (dotA8 a b)))
        (knotStoreF ρ₀) κ) :=
  stepIter_chain (mapply_elem_pre ρ₀ qf qx ρT a b κ)
    (elem_fire (knotStoreF ρ₀) a b κ)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, element·closure**: the machine defaults; so does META,
    to the representing value — the element itself a passenger
    (every probe on the way tests a tag). -/
theorem mapply_elem_clos (ρ₀ : Env) (qf qx ρT q' ρT' : Val) (a : Fin 8)
    (κ : Kont) :
    stepIter 190 (.ret (.cell (.elem 3) (.cell q' ρT')) (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, element·cell**: default agreement again, element a
    passenger. -/
theorem mapply_elem_cell (ρ₀ : Env) (qf qx ρT aT dT : Val) (a : Fin 8)
    (κ : Kont) :
    stepIter 149 (.ret (.cell (.elem 6) (.cell aT dT)) (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, element·location**: default agreement again, element
    and location both passengers. -/
theorem mapply_elem_loc (ρ₀ : Env) (qf qx ρT : Val) (a : Fin 8) (l : Nat)
    (κ : Kont) :
    stepIter 149 (.ret (.cell (.elem 5) (.loc l)) (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, cell function**: the machine defaults on applying a
    pair; META's fallback arm agrees, whatever the argument. -/
theorem mapply_cellf (ρ₀ : Env) (qf qx ρT aT dT vxT : Val) (κ : Kont) :
    stepIter 159 (.ret vxT (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 6) (.cell aT dT)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Apply, location function**: default agreement, whatever the
    argument and the location. -/
theorem mapply_locf (ρ₀ : Env) (qf qx ρT vxT : Val) (l : Nat) (κ : Kont) :
    stepIter 159 (.ret vxT (knotStoreF ρ₀)
        (appKx ρ₀ qf qx ρT (.cell (.elem 5) (.loc l)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

/-! ## Right-side inversions

The master induction learns a value's *direct* shape from `EvP` and
needs the *tagged* shape. These invert the relation from the right,
with equation-shaped conclusions (robust under `subst`, whichever
way `cases` orients the forced unifications). -/

theorem elemR_inv {vT : Val} {a : Fin 8}
    (h : RepV 14 KRempty vT (.elem a)) :
    vT = .cell (.elem 2) (.elem a) := by
  cases h; rfl

theorem closR_inv {vT : Val} {b : Prog} {ρ' : Env}
    (h : RepV 14 KRempty vT (.clos b ρ')) :
    ∃ ρT', vT = .cell (.elem 3) (.cell (quoteD b) ρT') ∧
      RepEnv 14 KRempty ρT' ρ' := by
  cases h with | clos _ hρ => exact ⟨_, rfl, hρ⟩

theorem kontR_inv {vT : Val} {κ' : Kont}
    (h : RepV 14 KRempty vT (.cont κ')) : False := by
  cases h with | kont hκ => exact hκ

theorem cellR_inv {vT a d : Val}
    (h : RepV 14 KRempty vT (.cell a d)) :
    ∃ aT dT, vT = .cell (.elem 6) (.cell aT dT) := by
  cases h with | cell ha hd => exact ⟨_, _, rfl⟩

theorem locR_inv {vT : Val} {l : Nat}
    (h : RepV 14 KRempty vT (.loc l)) :
    vT = .cell (.elem 5) (.loc (14 + l)) := by
  cases h; rfl

/-! ## The master theorem -/

/-- **The general simulation induction.** For every big-step
    derivation of the pure fragment, every represented environment,
    every initial environment, and every continuation: META's
    recursive interpretation reaches the return of a value
    representing the machine's, over the unchanged knot store.
    Induction on the derivation; the dispatch kit glues the
    sub-runs. -/
theorem meval_sim {p : Prog} {ρ : Env} {v : Val} (h : EvP p ρ v) :
    ∀ (ρ₀ : Env) {ρT : Val}, RepEnv 14 KRempty ρT ρ → ∀ κ : Kont,
      ∃ (n : Nat) (vT : Val), RepV 14 KRempty vT v ∧
        stepIter n (mevalCall ρ₀ (quoteD p) ρT κ) =
          .inl (.ret vT (knotStoreF ρ₀) κ) := by
  induction h with
  | atom a ρ =>
    intro ρ₀ ρT hρ κ
    exact ⟨atomSteps a, _, .elem a, meval_atom ρ₀ a ρT κ⟩
  | var n ρ =>
    intro ρ₀ ρT hρ κ
    obtain ⟨m, hm⟩ := mnth_sim ρ₀ n hρ κ
    exact ⟨116 + m, _, hρ.chainNth n,
      stepIter_chain (meval_var_dispatch ρ₀ (natToVal n) ρT κ) hm⟩
  | lam b ρ =>
    intro ρ₀ ρT hρ κ
    exact ⟨115, _, .clos b hρ, meval_lam ρ₀ (quoteD b) ρT κ⟩
  | @appClos f x b ρ ρ' vx v _ _ _ ihf ihx ihb =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨ρTf, rfl, hρ'⟩ := closR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
    obtain ⟨nb, vT, repB, runB⟩ := ihb ρ₀ (.cons repX hρ') κ
    exact ⟨129 + (nf + (29 + (nx + (214 + nb)))), vT, repB,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
            (stepIter_chain runX
              (stepIter_chain
                (mapply_clos ρ₀ (quoteD f) (quoteD x) ρT
                  (quoteD b) ρTf vxT κ) runB))))⟩
  | @appElem f x ρ a b _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    obtain rfl := elemR_inv repX
    exact ⟨129 + (nf + (29 + (nx + 198))), _, .elem (dotA8 a b),
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 2) (.elem a)) κ)
            (stepIter_chain runX
              (mapply_elem_elem ρ₀ (quoteD f) (quoteD x) ρT a b κ))))⟩
  | @appElemErr f x ρ a w _ _ hw ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cont κ' => exact (kontR_inv repX).elim
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 190))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_clos ρ₀ (quoteD f) (quoteD x) ρT
                  (quoteD b') ρTx a κ))))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_cell ρ₀ (quoteD f) (quoteD x) ρT
                  aT dT a κ))))⟩
    | loc l' =>
      obtain rfl := locR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_loc ρ₀ (quoteD f) (quoteD x) ρT
                  a (14 + l') κ))))⟩
  | @appCellErr f x ρ a d w _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨aT, dT, rfl⟩ := cellR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 6) (.cell aT dT)) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, .elem 0,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 6) (.cell aT dT)) κ)
            (stepIter_chain runX
              (mapply_cellf ρ₀ (quoteD f) (quoteD x) ρT aT dT vxT κ))))⟩
  | @appLocErr f x ρ l w _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := locR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 5) (.loc (14 + l))) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, .elem 0,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 5) (.loc (14 + l))) κ)
            (stepIter_chain runX
              (mapply_locf ρ₀ (quoteD f) (quoteD x) ρT vxT (14 + l) κ))))⟩

/-! ## Top-level adequacy -/

/-- **Adequacy for the pure fragment**: from one big-step
    derivation of a closed pure program — the meta run converges,
    the direct run converges, and the two values stand in the
    representation relation. The 3b(ii)/(iii) families are
    instances; no per-family kernel reduction remains. -/
theorem adequacy_pure {p : Prog} {v : Val} (h : EvP p [] v) :
    ∃ (n : Nat) (vT : Val), RepV 14 KRempty vT v ∧
      loop n (metaState p) = some vT ∧
      ∃ m, runM m [] [] p = some v := by
  obtain ⟨n, vT, rep, run⟩ := meval_sim h [quoteD p] .nil .halt
  obtain ⟨m, hm⟩ := evp_steps h [] .halt
  have lastM : stepIter 1 (.ret vT (knotStoreF [quoteD p]) .halt) =
      .inr vT := rfl
  have lastD : stepIter 1 (.ret v [] .halt) = .inr v := rfl
  exact ⟨entrySteps + (17 + (n + 1)), vT, rep,
    loop_of_stepIter_inr
      (stepIter_chain (meval_entry p)
        (stepIter_chain (call_entry p) (stepIter_chain run lastM))),
    m + 1, loop_of_stepIter_inr (stepIter_chain hm lastD)⟩

/-- **The interpreted magma is the magma**: for every pair of
    atoms, META applied to `⌜a · b⌝` computes the tagged table
    product the machine computes directly — all 64 products, with
    no kernel reduction left in this corollary: it is an instance
    of the master theorem. -/
theorem adequacy_product (a b : Fin 8) :
    ∃ n, loop n (metaState (.app (.atom a) (.atom b))) =
      some (.cell (.elem 2) (.elem (dotA8 a b))) ∧
    ∃ m, runM m [] [] (.app (.atom a) (.atom b)) =
      some (.elem (dotA8 a b)) := by
  obtain ⟨n, vT, rep, hloop, m, hrun⟩ :=
    adequacy_pure (EvP.appElem (EvP.atom a []) (EvP.atom b []))
  obtain rfl := elemR_inv rep
  exact ⟨n, hloop, m, hrun⟩

/-! ## A family infinite in structure

What no finite collection of per-skeleton reductions could state:
adequacy for a program family of *unbounded nesting depth*. -/

/-- The identity combinator, applied `k` times to `var n`. -/
def idTower : Nat → Nat → Prog
  | 0, n => .var n
  | k + 1, n => .app (.lam (.var 0)) (idTower k n)

/-- Every id-tower evaluates (big-step) to the error default: the
    variable misses in the empty environment, and each identity
    layer passes the value through. -/
theorem idTower_evp (k n : Nat) : EvP (idTower k n) [] (.elem 0) := by
  induction k with
  | zero => exact EvP.var n []
  | succ k ih =>
    exact EvP.appClos (EvP.lam _ _) ih (EvP.var 0 [.elem 0])

/-- **Adequacy at every nesting depth and every index**: a family
    doubly infinite — in program *structure* and in the leaf — from
    the simulation induction. The β families of 3b(iii) are the
    `k = 1` slice. -/
theorem adequacy_id_tower (k n : Nat) :
    ∃ (fuel : Nat) (vT : Val), RepV 14 KRempty vT (.elem 0) ∧
      loop fuel (metaState (idTower k n)) = some vT ∧
      ∃ m, runM m [] [] (idTower k n) = some (.elem 0) :=
  adequacy_pure (idTower_evp k n)

end AdequacySim
end Dichotomic

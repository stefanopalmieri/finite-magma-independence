import Magma.AdequacyStoreKit

/-!
# Adequacy campaign, rung 5: the store forms

The simulation induction over **live stores**. `EvS` threads a store
through every judgment — seventeen clauses from rungs 3b(iv)/4 plus
`ref`, `deref` (location and error arms), and `setref` (location and
error arms) — and the master `meval_simS` carries rung 2's alignment
as its invariant: META's store is always the knot prefix followed by
a pointwise-represented image of the machine's, and the canonical
location map `i ↦ K₀ + i` is *forced by the machine's own
allocation rule* (`ref_alloc`): META allocates exactly when the
object program allocates, at the length of a store that carries the
prefix. Rung 2's algebra (`set_append_right'`, `forall₂_append`,
`forall₂_set`) does the store bookkeeping; the kit's `rfl`s do the
running.

One honest boundary, discovered at statement time: `derefLoc`
carries an in-bounds premise. On an *out-of-bounds* read the two
worlds' defaults differ in kind — the machine returns `elem 0`, and
META's host-level read returns the same *naked* `elem 0` where its
convention needs the tagged `(quo.tt)` — so the relation cannot pair
them. Machine-created locations are always in bounds (stores only
grow, and `ref` allocates at the length), so the gap is
representable-but-unreachable; a store well-formedness invariant can
lift it later. `setref` out of bounds is a no-op in *both* worlds
and needs no guard.

Corollaries: `adequacy_store` (closed programs of the 12-form
fragment, from the empty store — final stores related pointwise),
`adequacy_ref_deref` (the store roundtrip through the interpreter,
all eight elements), `adequacy_setref` (allocate, overwrite, and the
written value returns — all 64 pairs).
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyStore

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep
  AdequacyLeaf AdequacySim AdequacyData AdequacyStoreKit

/-! ## The big-step relation, store-threading -/

/-- Big-step evaluation for the 12-form fragment (pure + data +
    store), matching the machine arm for arm. `derefLoc` carries the
    in-bounds premise (see the module docstring). -/
inductive EvS : Prog → Env → Store → Val → Store → Prop where
  | atom (a : Fin 8) (ρ : Env) (σ : Store) : EvS (.atom a) ρ σ (.elem a) σ
  | var (n : Nat) (ρ : Env) (σ : Store) :
      EvS (.var n) ρ σ (ρ.getD n (.elem 0)) σ
  | lam (b : Prog) (ρ : Env) (σ : Store) : EvS (.lam b) ρ σ (.clos b ρ) σ
  | appClos {f x b : Prog} {ρ ρ' : Env} {σ σ₁ σ₂ σ₃ : Store} {vx v : Val} :
      EvS f ρ σ (.clos b ρ') σ₁ → EvS x ρ σ₁ vx σ₂ →
      EvS b (vx :: ρ') σ₂ v σ₃ → EvS (.app f x) ρ σ v σ₃
  | appElem {f x : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {a b : Fin 8} :
      EvS f ρ σ (.elem a) σ₁ → EvS x ρ σ₁ (.elem b) σ₂ →
      EvS (.app f x) ρ σ (.elem (dotA8 a b)) σ₂
  | appElemErr {f x : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {a : Fin 8} {w : Val} :
      EvS f ρ σ (.elem a) σ₁ → EvS x ρ σ₁ w σ₂ →
      (∀ b : Fin 8, w ≠ .elem b) → EvS (.app f x) ρ σ (.elem 0) σ₂
  | appCellErr {f x : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {a d w : Val} :
      EvS f ρ σ (.cell a d) σ₁ → EvS x ρ σ₁ w σ₂ →
      EvS (.app f x) ρ σ (.elem 0) σ₂
  | appLocErr {f x : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {l : Nat} {w : Val} :
      EvS f ρ σ (.loc l) σ₁ → EvS x ρ σ₁ w σ₂ →
      EvS (.app f x) ρ σ (.elem 0) σ₂
  | cons {a b : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {va vb : Val} :
      EvS a ρ σ va σ₁ → EvS b ρ σ₁ vb σ₂ →
      EvS (.cons a b) ρ σ (.cell va vb) σ₂
  | carCell {e : Prog} {ρ : Env} {σ σ₁ : Store} {u w : Val} :
      EvS e ρ σ (.cell u w) σ₁ → EvS (.car e) ρ σ u σ₁
  | carErr {e : Prog} {ρ : Env} {σ σ₁ : Store} {w : Val} :
      EvS e ρ σ w σ₁ → (∀ u v, w ≠ .cell u v) →
      EvS (.car e) ρ σ (.elem 0) σ₁
  | cdrCell {e : Prog} {ρ : Env} {σ σ₁ : Store} {u w : Val} :
      EvS e ρ σ (.cell u w) σ₁ → EvS (.cdr e) ρ σ w σ₁
  | cdrErr {e : Prog} {ρ : Env} {σ σ₁ : Store} {w : Val} :
      EvS e ρ σ w σ₁ → (∀ u v, w ≠ .cell u v) →
      EvS (.cdr e) ρ σ (.elem 0) σ₁
  | pairpYes {e : Prog} {ρ : Env} {σ σ₁ : Store} {u w : Val} :
      EvS e ρ σ (.cell u w) σ₁ → EvS (.pairp e) ρ σ (.elem 0) σ₁
  | pairpNo {e : Prog} {ρ : Env} {σ σ₁ : Store} {w : Val} :
      EvS e ρ σ w σ₁ → (∀ u v, w ≠ .cell u v) →
      EvS (.pairp e) ρ σ (.elem 1) σ₁
  | iteFf {c t e : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {v : Val} :
      EvS c ρ σ (.elem 1) σ₁ → EvS e ρ σ₁ v σ₂ →
      EvS (.ite c t e) ρ σ v σ₂
  | iteElem {c t e : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {b : Fin 8} {v : Val} :
      EvS c ρ σ (.elem b) σ₁ → b ≠ 1 → EvS t ρ σ₁ v σ₂ →
      EvS (.ite c t e) ρ σ v σ₂
  | iteVal {c t e : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {w v : Val} :
      EvS c ρ σ w σ₁ → (∀ b : Fin 8, w ≠ .elem b) → EvS t ρ σ₁ v σ₂ →
      EvS (.ite c t e) ρ σ v σ₂
  | ref {e : Prog} {ρ : Env} {σ σ₁ : Store} {v : Val} :
      EvS e ρ σ v σ₁ → EvS (.ref e) ρ σ (.loc σ₁.length) (σ₁ ++ [v])
  | derefLoc {e : Prog} {ρ : Env} {σ σ₁ : Store} {n : Nat} :
      EvS e ρ σ (.loc n) σ₁ → n < σ₁.length →
      EvS (.deref e) ρ σ (σ₁.getD n (.elem 0)) σ₁
  | derefErr {e : Prog} {ρ : Env} {σ σ₁ : Store} {w : Val} :
      EvS e ρ σ w σ₁ → (∀ n, w ≠ .loc n) →
      EvS (.deref e) ρ σ (.elem 0) σ₁
  | setLoc {l e : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {n : Nat} {w : Val} :
      EvS l ρ σ (.loc n) σ₁ → EvS e ρ σ₁ w σ₂ →
      EvS (.setref l e) ρ σ w (σ₂.set n w)
  | setErr {l e : Prog} {ρ : Env} {σ σ₁ σ₂ : Store} {vl w : Val} :
      EvS l ρ σ vl σ₁ → (∀ n, vl ≠ .loc n) → EvS e ρ σ₁ w σ₂ →
      EvS (.setref l e) ρ σ (.elem 0) σ₂

/-- The store-free relation embeds: an `EvD` derivation runs at any
    store, unchanged. -/
theorem evD_evS {p : Prog} {ρ : Env} {v : Val} (h : EvD p ρ v) :
    ∀ σ : Store, EvS p ρ σ v σ := by
  induction h with
  | atom a ρ => exact fun σ => .atom a ρ σ
  | var n ρ => exact fun σ => .var n ρ σ
  | lam b ρ => exact fun σ => .lam b ρ σ
  | appClos _ _ _ ihf ihx ihb =>
    exact fun σ => .appClos (ihf σ) (ihx σ) (ihb σ)
  | appElem _ _ ihf ihx => exact fun σ => .appElem (ihf σ) (ihx σ)
  | appElemErr _ _ hw ihf ihx =>
    exact fun σ => .appElemErr (ihf σ) (ihx σ) hw
  | appCellErr _ _ ihf ihx => exact fun σ => .appCellErr (ihf σ) (ihx σ)
  | appLocErr _ _ ihf ihx => exact fun σ => .appLocErr (ihf σ) (ihx σ)
  | cons _ _ iha ihb => exact fun σ => .cons (iha σ) (ihb σ)
  | carCell _ ihe => exact fun σ => .carCell (ihe σ)
  | carErr _ hw ihe => exact fun σ => .carErr (ihe σ) hw
  | cdrCell _ ihe => exact fun σ => .cdrCell (ihe σ)
  | cdrErr _ hw ihe => exact fun σ => .cdrErr (ihe σ) hw
  | pairpYes _ ihe => exact fun σ => .pairpYes (ihe σ)
  | pairpNo _ hw ihe => exact fun σ => .pairpNo (ihe σ) hw
  | iteFf _ _ ihc ihe => exact fun σ => .iteFf (ihc σ) (ihe σ)
  | iteElem _ hb _ ihc iht => exact fun σ => .iteElem (ihc σ) hb (iht σ)
  | iteVal _ hw _ ihc iht => exact fun σ => .iteVal (ihc σ) hw (iht σ)

/-! ## Machine soundness -/

/-- `EvS` is sound for the machine, at every continuation. -/
theorem evS_steps {p : Prog} {ρ : Env} {σ : Store} {v : Val} {σ₂ : Store}
    (h : EvS p ρ σ v σ₂) :
    ∀ κ : Kont, ∃ n, stepIter n (.eval p ρ σ κ) = .inl (.ret v σ₂ κ) := by
  induction h with
  | atom a ρ σ => exact fun κ => ⟨1, rfl⟩
  | var n ρ σ => exact fun κ => ⟨1, rfl⟩
  | lam b ρ σ => exact fun κ => ⟨1, rfl⟩
  | @appClos f x b ρ ρ' σ σ₁ σ₂ σ₃ vx v _ _ _ ihf ihx ihb =>
    intro κ
    obtain ⟨nf, hf⟩ := ihf (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx (.appR (.clos b ρ') κ)
    obtain ⟨nb, hb⟩ := ihb κ
    exact ⟨1 + (nf + (1 + (nx + (1 + nb)))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx (stepIter_chain rfl hb))))⟩
  | @appElem f x ρ σ σ₁ σ₂ a b _ _ ihf ihx =>
    intro κ
    obtain ⟨nf, hf⟩ := ihf (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx (.appR (.elem a) κ)
    exact ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx rfl)))⟩
  | @appElemErr f x ρ σ σ₁ σ₂ a w _ _ hw ihf ihx =>
    intro κ
    obtain ⟨nf, hf⟩ := ihf (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx (.appR (.elem a) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @appCellErr f x ρ σ σ₁ σ₂ a d w _ _ ihf ihx =>
    intro κ
    obtain ⟨nf, hf⟩ := ihf (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx (.appR (.cell a d) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl
  | @appLocErr f x ρ σ σ₁ σ₂ l w _ _ ihf ihx =>
    intro κ
    obtain ⟨nf, hf⟩ := ihf (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx (.appR (.loc l) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl
  | @cons a b ρ σ σ₁ σ₂ va vb _ _ iha ihb =>
    intro κ
    obtain ⟨na, ha⟩ := iha (.consL b ρ κ)
    obtain ⟨nb, hb⟩ := ihb (.consR va κ)
    exact ⟨1 + (na + (1 + (nb + 1))),
      stepIter_chain rfl (stepIter_chain ha (stepIter_chain rfl
        (stepIter_chain hb rfl)))⟩
  | @carCell e ρ σ σ₁ u w _ ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.carK κ)
    exact ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @carErr e ρ σ σ₁ w _ hw ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.carK κ)
    refine ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @cdrCell e ρ σ σ₁ u w _ ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.cdrK κ)
    exact ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @cdrErr e ρ σ σ₁ w _ hw ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.cdrK κ)
    refine ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @pairpYes e ρ σ σ₁ u w _ ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.pairK κ)
    exact ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @pairpNo e ρ σ σ₁ w _ hw ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.pairK κ)
    refine ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @iteFf c t e ρ σ σ₁ σ₂ v _ _ ihc ihe =>
    intro κ
    obtain ⟨nc, hc⟩ := ihc (.iteK t e ρ κ)
    obtain ⟨ne, he⟩ := ihe κ
    exact ⟨1 + (nc + (1 + ne)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain rfl he))⟩
  | @iteElem c t e ρ σ σ₁ σ₂ b v _ hb _ ihc iht =>
    intro κ
    obtain ⟨nc, hc⟩ := ihc (.iteK t e ρ κ)
    obtain ⟨nt, ht⟩ := iht κ
    have h1 : stepIter 1 (.ret (.elem b) σ₁ (.iteK t e ρ κ)) =
        .inl (.eval (if b = 1 then e else t) ρ σ₁ κ) := rfl
    rw [if_neg hb] at h1
    exact ⟨1 + (nc + (1 + nt)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain h1 ht))⟩
  | @iteVal c t e ρ σ σ₁ σ₂ w v _ hw _ ihc iht =>
    intro κ
    obtain ⟨nc, hc⟩ := ihc (.iteK t e ρ κ)
    obtain ⟨nt, ht⟩ := iht κ
    refine ⟨1 + (nc + (1 + nt)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain ?_ ht))⟩
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @ref e ρ σ σ₁ v _ ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.refK κ)
    exact ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @derefLoc e ρ σ σ₁ n _ hn ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.derefK κ)
    exact ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @derefErr e ρ σ σ₁ w _ hw ihe =>
    intro κ
    obtain ⟨ne, he⟩ := ihe (.derefK κ)
    refine ⟨1 + (ne + 1), stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | loc n => exact absurd rfl (hw n)
    | elem _ => rfl
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
  | @setLoc l e ρ σ σ₁ σ₂ n w _ _ ihl ihe =>
    intro κ
    obtain ⟨nl, hl⟩ := ihl (.setL e ρ κ)
    obtain ⟨ne, he⟩ := ihe (.setR (.loc n) κ)
    exact ⟨1 + (nl + (1 + (ne + 1))),
      stepIter_chain rfl (stepIter_chain hl (stepIter_chain rfl
        (stepIter_chain he rfl)))⟩
  | @setErr l e ρ σ σ₁ σ₂ vl w _ hw _ ihl ihe =>
    intro κ
    obtain ⟨nl, hl⟩ := ihl (.setL e ρ κ)
    obtain ⟨ne, he⟩ := ihe (.setR vl κ)
    refine ⟨1 + (nl + (1 + (ne + 1))),
      stepIter_chain rfl (stepIter_chain hl (stepIter_chain rfl
        (stepIter_chain he ?_)))⟩
    cases vl with
    | loc n => exact absurd rfl (hw n)
    | elem _ => rfl
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl

/-! ## The deep `setref` split

These two live here rather than in the kit: their types embed the
*triple-nested* transformer (`setKp` runs `setKx` runs `setKl`), the
deepest reductions in the campaign, and they carry the ten-fold
heartbeat budget the `fin_cases` lemmas taught us to expect. -/

/-- The frames above `setref`'s naked write. The written value is a
    **parameter**: META's post-write continuation closure captures
    the incoming value in its environment before the write fires —
    the first value in the campaign that is *not* a passenger
    through its frames (the `rfl` refuted the dummy-extracted
    version). -/
def setKp (ρ₀ : Env) (ql qe ρT wT : Val) (j : Nat) (κ : Kont) : Kont :=
  projSetR (stepIter 68 (.ret wT (knotStoreF ρ₀)
    (setKx ρ₀ ql qe ρT (.cell (.elem 5) (.loc j)) κ)))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **`setref` on a location, approach**: 68 steps from the written
    value's return to the naked write — the location re-emerging in
    the machine's own `setR` frame, the written value captured in
    the frames above it. -/
theorem set_pre_S (ρ₀ : Env) (σ' : Store) (ql qe ρT wT : Val) (j : Nat)
    (κ : Kont) :
    stepIter 68 (.ret wT (knotStoreF ρ₀ ++ σ')
        (setKx ρ₀ ql qe ρT (.cell (.elem 5) (.loc j)) κ)) =
      .inl (.ret wT (knotStoreF ρ₀ ++ σ')
        (.setR (.loc j) (setKp ρ₀ ql qe ρT wT j κ))) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **`setref` unwind**: 2 steps over the written store — which is
    fully symbolic here: the unwind provably never reads it. -/
theorem set_post_S (ρ₀ : Env) (σw : Store) (ql qe ρT wT : Val)
    (j : Nat) (κ : Kont) :
    stepIter 2 (.ret wT σw (setKp ρ₀ ql qe ρT wT j κ)) =
      .inl (.ret wT σw κ) :=
  rfl

/-! ## Store-side plumbing -/

/-- In-bounds reads of related stores are related (defaults
    irrelevant). -/
theorem forall₂_getD {σT σ : Store}
    (hF : List.Forall₂ (RepV 14 KRempty) σT σ)
    {n : Nat} (hn : n < σ.length) (d d' : Val) :
    RepV 14 KRempty (σT.getD n d) (σ.getD n d') := by
  have h : σ[n]? = some σ[n] := List.getElem?_eq_getElem hn
  obtain ⟨vT', hvT', hR⟩ := forall₂_getElem? hF h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h, hvT']
  exact hR

/-! ## The master theorem over live stores -/

/-- **The simulation induction, stores engaged.** For every
    store-threading big-step derivation, every represented
    environment, every pointwise-represented store suffix, and
    every continuation: META's run reaches the return of a
    representing value over the knot prefix plus a suffix
    representing the final store. Rung 2's alignment, as the
    induction invariant it was built to be. -/
theorem meval_simS {p : Prog} {ρ : Env} {σ : Store} {v : Val}
    {σ₂ : Store} (h : EvS p ρ σ v σ₂) :
    ∀ (ρ₀ : Env) {ρT : Val}, RepEnv 14 KRempty ρT ρ →
    ∀ {σT : Store}, List.Forall₂ (RepV 14 KRempty) σT σ →
    ∀ κ : Kont,
      ∃ (n : Nat) (vT : Val) (σT₂ : Store),
        List.Forall₂ (RepV 14 KRempty) σT₂ σ₂ ∧
        RepV 14 KRempty vT v ∧
        stepIter n (mevalCallS ρ₀ σT (quoteD p) ρT κ) =
          .inl (.ret vT (knotStoreF ρ₀ ++ σT₂) κ) := by
  induction h with
  | atom a ρ σ =>
    intro ρ₀ ρT hρ σT hF κ
    exact ⟨atomSteps a, _, σT, hF, .elem a, meval_atom_S ρ₀ σT a ρT κ⟩
  | var n ρ σ =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨m, hm⟩ := mnth_sim_S ρ₀ σT n hρ κ
    exact ⟨116 + m, _, σT, hF, hρ.chainNth n,
      stepIter_chain (meval_var_dispatch_S ρ₀ σT (natToVal n) ρT κ) hm⟩
  | lam b ρ σ =>
    intro ρ₀ ρT hρ σT hF κ
    exact ⟨115, _, σT, hF, .clos b hρ, meval_lam_S ρ₀ σT (quoteD b) ρT κ⟩
  | @appClos f x b ρ ρ' σ σ₁ σ₂ σ₃ vx v _ _ _ ihf ihx ihb =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nf, vfT, σT₁, hF₁, repF, runF⟩ :=
      ihf ρ₀ hρ hF (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨ρTf, rfl, hρ'⟩ := closR_inv repF
    obtain ⟨nx, vxT, σT₂, hF₂, repX, runX⟩ :=
      ihx ρ₀ hρ hF₁ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
    obtain ⟨nb, vT, σT₃, hF₃, repB, runB⟩ :=
      ihb ρ₀ (.cons repX hρ') hF₂ κ
    exact ⟨129 + (nf + (29 + (nx + (214 + nb)))), vT, σT₃, hF₃, repB,
      stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
              (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
            (stepIter_chain runX
              (stepIter_chain
                (mapply_clos_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                  (quoteD b) ρTf vxT κ) runB))))⟩
  | @appElem f x ρ σ σ₁ σ₂ a b _ _ ihf ihx =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nf, vfT, σT₁, hF₁, repF, runF⟩ :=
      ihf ρ₀ hρ hF (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, σT₂, hF₂, repX, runX⟩ :=
      ihx ρ₀ hρ hF₁ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    obtain rfl := elemR_inv repX
    exact ⟨129 + (nf + (29 + (nx + 198))), _, σT₂, hF₂,
      .elem (dotA8 a b),
      stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
              (.cell (.elem 2) (.elem a)) κ)
            (stepIter_chain runX
              (mapply_elem_elem_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                a b κ))))⟩
  | @appElemErr f x ρ σ σ₁ σ₂ a w _ _ hw ihf ihx =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nf, vfT, σT₁, hF₁, repF, runF⟩ :=
      ihf ρ₀ hρ hF (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, σT₂, hF₂, repX, runX⟩ :=
      ihx ρ₀ hρ hF₁ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cont κ' => exact (kontR_inv repX).elim
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 190))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_clos_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                  (quoteD b') ρTx a κ))))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_cell_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                  aT dT a κ))))⟩
    | loc l' =>
      obtain rfl := locR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_loc_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                  a (14 + l') κ))))⟩
  | @appCellErr f x ρ σ σ₁ σ₂ a d w _ _ ihf ihx =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nf, vfT, σT₁, hF₁, repF, runF⟩ :=
      ihf ρ₀ hρ hF (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨aT, dT, rfl⟩ := cellR_inv repF
    obtain ⟨nx, vxT, σT₂, hF₂, repX, runX⟩ :=
      ihx ρ₀ hρ hF₁ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 6) (.cell aT dT)) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, σT₂, hF₂, .elem 0,
      stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
              (.cell (.elem 6) (.cell aT dT)) κ)
            (stepIter_chain runX
              (mapply_cellf_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                aT dT vxT κ))))⟩
  | @appLocErr f x ρ σ σ₁ σ₂ l w _ _ ihf ihx =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nf, vfT, σT₁, hF₁, repF, runF⟩ :=
      ihf ρ₀ hρ hF (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := locR_inv repF
    obtain ⟨nx, vxT, σT₂, hF₂, repX, runX⟩ :=
      ihx ρ₀ hρ hF₁ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 5) (.loc (14 + l))) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, σT₂, hF₂, .elem 0,
      stepIter_chain (meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x_S ρ₀ σT₁ (quoteD f) (quoteD x) ρT
              (.cell (.elem 5) (.loc (14 + l))) κ)
            (stepIter_chain runX
              (mapply_locf_S ρ₀ σT₂ (quoteD f) (quoteD x) ρT
                vxT (14 + l) κ))))⟩
  | @cons a b ρ σ σ₁ σ₂ va vb _ _ iha ihb =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨na, vaT, σT₁, hF₁, repA, runA⟩ :=
      iha ρ₀ hρ hF (consKf ρ₀ (quoteD a) (quoteD b) ρT κ)
    obtain ⟨nb, vbT, σT₂, hF₂, repB, runB⟩ :=
      ihb ρ₀ hρ hF₁ (consKx ρ₀ (quoteD a) (quoteD b) ρT vaT κ)
    exact ⟨223 + (na + (20 + (nb + 2))), _, σT₂, hF₂,
      .cell repA repB,
      stepIter_chain (meval_cons_a_S ρ₀ σT (quoteD a) (quoteD b) ρT κ)
        (stepIter_chain runA
          (stepIter_chain
            (meval_cons_b_S ρ₀ σT₁ (quoteD a) (quoteD b) ρT vaT κ)
            (stepIter_chain runB
              (cons_pack_S ρ₀ σT₂ (quoteD a) (quoteD b) ρT
                vaT vbT κ))))⟩
  | @carCell e ρ σ σ₁ u w _ ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (carKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, ha, hd⟩ := cellR_inv' repE
    exact ⟨220 + (ne + 64), aT, σT₁, hF₁, ha,
      stepIter_chain (meval_car_e_S ρ₀ σT (quoteD e) ρT κ)
        (stepIter_chain runE
          (mcar_cell_S ρ₀ σT₁ (quoteD e) ρT aT dT κ))⟩
  | @carErr e ρ σ σ₁ w _ hw ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (carKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨220 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_car_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcar_elem_S ρ₀ σT₁ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨220 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_car_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcar_clos_S ρ₀ σT₁ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨220 + (ne + 64), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_car_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcar_loc_S ρ₀ σT₁ (quoteD e) ρT (14 + l') κ))⟩
  | @cdrCell e ρ σ σ₁ u w _ ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (cdrKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, ha, hd⟩ := cellR_inv' repE
    exact ⟨213 + (ne + 64), dT, σT₁, hF₁, hd,
      stepIter_chain (meval_cdr_e_S ρ₀ σT (quoteD e) ρT κ)
        (stepIter_chain runE
          (mcdr_cell_S ρ₀ σT₁ (quoteD e) ρT aT dT κ))⟩
  | @cdrErr e ρ σ σ₁ w _ hw ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (cdrKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨213 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_cdr_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcdr_elem_S ρ₀ σT₁ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨213 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_cdr_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcdr_clos_S ρ₀ σT₁ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨213 + (ne + 64), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_cdr_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcdr_loc_S ρ₀ σT₁ (quoteD e) ρT (14 + l') κ))⟩
  | @pairpYes e ρ σ σ₁ u w _ ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (pairKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, _, _⟩ := cellR_inv' repE
    exact ⟨186 + (ne + 64), _, σT₁, hF₁, .elem 0,
      stepIter_chain (meval_pairp_e_S ρ₀ σT (quoteD e) ρT κ)
        (stepIter_chain runE
          (mpairp_cell_S ρ₀ σT₁ (quoteD e) ρT aT dT κ))⟩
  | @pairpNo e ρ σ σ₁ w _ hw ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (pairKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨186 + (ne + 57), _, σT₁, hF₁, .elem 1,
        stepIter_chain (meval_pairp_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mpairp_elem_S ρ₀ σT₁ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨186 + (ne + 57), _, σT₁, hF₁, .elem 1,
        stepIter_chain (meval_pairp_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mpairp_clos_S ρ₀ σT₁ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨186 + (ne + 64), _, σT₁, hF₁, .elem 1,
        stepIter_chain (meval_pairp_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mpairp_loc_S ρ₀ σT₁ (quoteD e) ρT (14 + l') κ))⟩
  | @iteFf c t e ρ σ σ₁ σ₂ v _ _ ihc ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nc, vcT, σT₁, hF₁, repC, runC⟩ :=
      ihc ρ₀ hρ hF (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain rfl := elemR_inv repC
    obtain ⟨ne, veT, σT₂, hF₂, repE, runE⟩ := ihe ρ₀ hρ hF₁ κ
    exact ⟨188 + (nc + (119 + ne)), veT, σT₂, hF₂, repE,
      stepIter_chain
        (meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κ)
        (stepIter_chain runC
          (stepIter_chain
            (mite_ff_S ρ₀ σT₁ (quoteD c) (quoteD t) (quoteD e) ρT κ)
            runE))⟩
  | @iteElem c t e ρ σ σ₁ σ₂ b v _ hb _ ihc iht =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nc, vcT, σT₁, hF₁, repC, runC⟩ :=
      ihc ρ₀ hρ hF (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain rfl := elemR_inv repC
    obtain ⟨nt, vtT, σT₂, hF₂, repT, runT⟩ := iht ρ₀ hρ hF₁ κ
    exact ⟨188 + (nc + (119 + nt)), vtT, σT₂, hF₂, repT,
      stepIter_chain
        (meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κ)
        (stepIter_chain runC
          (stepIter_chain
            (mite_elem_tt_S ρ₀ σT₁ (quoteD c) (quoteD t) (quoteD e)
              ρT b hb κ) runT))⟩
  | @iteVal c t e ρ σ σ₁ σ₂ w v _ hw _ ihc iht =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nc, vcT, σT₁, hF₁, repC, runC⟩ :=
      ihc ρ₀ hρ hF (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain ⟨nt, vtT, σT₂, hF₂, repT, runT⟩ := iht ρ₀ hρ hF₁ κ
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cont κ' => exact (kontR_inv repC).elim
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repC
      exact ⟨188 + (nc + (114 + nt)), vtT, σT₂, hF₂, repT,
        stepIter_chain
          (meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_clos_S ρ₀ σT₁ (quoteD c) (quoteD t) (quoteD e)
                ρT (quoteD b') ρTx κ) runT))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repC
      exact ⟨188 + (nc + (73 + nt)), vtT, σT₂, hF₂, repT,
        stepIter_chain
          (meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_cell_S ρ₀ σT₁ (quoteD c) (quoteD t) (quoteD e)
                ρT aT dT κ) runT))⟩
    | loc l' =>
      obtain rfl := locR_inv repC
      exact ⟨188 + (nc + (73 + nt)), vtT, σT₂, hF₂, repT,
        stepIter_chain
          (meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_loc_S ρ₀ σT₁ (quoteD c) (quoteD t) (quoteD e)
                ρT (14 + l') κ) runT))⟩
  | @ref e ρ σ σ₁ v _ ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (.refK (.consR (.elem 5) κ))
    have hlen : (knotStoreF ρ₀ ++ σT₁).length = 14 + σ₁.length := by
      rw [List.length_append, knot_length ρ₀, hF₁.length_eq]
    have run2 := stepIter_chain (meval_ref_e_S ρ₀ σT (quoteD e) ρT κ)
      (stepIter_chain runE (ref_alloc (knotStoreF ρ₀ ++ σT₁) veT κ))
    rw [hlen, List.append_assoc] at run2
    exact ⟨194 + (ne + 2), _, σT₁ ++ [veT],
      forall₂_append hF₁ (List.Forall₂.cons repE List.Forall₂.nil),
      .loc σ₁.length, run2⟩
  | @derefLoc e ρ σ σ₁ n _ hn ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (derefKf ρ₀ (quoteD e) ρT κ)
    obtain rfl := locR_inv repE
    have hget : (knotStoreF ρ₀ ++ σT₁).getD (14 + n) (.elem 0) =
        σT₁.getD n (.elem 0) := by
      have h := getD_append_right' (knotStoreF ρ₀) σT₁ n (.elem 0)
      rwa [knot_length ρ₀] at h
    have run2 := stepIter_chain (meval_deref_e_S ρ₀ σT (quoteD e) ρT κ)
      (stepIter_chain runE
        (stepIter_chain (deref_pre_S ρ₀ σT₁ (quoteD e) ρT (14 + n) κ)
          (deref_read (knotStoreF ρ₀ ++ σT₁) (14 + n) κ)))
    rw [hget] at run2
    exact ⟨193 + (ne + (63 + 1)), _, σT₁, hF₁,
      forall₂_getD hF₁ hn _ _, run2⟩
  | @derefErr e ρ σ σ₁ w _ hw ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨ne, veT, σT₁, hF₁, repE, runE⟩ :=
      ihe ρ₀ hρ hF (derefKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | loc n => exact absurd rfl (hw n)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨193 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_deref_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mderef_elem_S ρ₀ σT₁ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨193 + (ne + 57), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_deref_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mderef_clos_S ρ₀ σT₁ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repE
      exact ⟨193 + (ne + 64), _, σT₁, hF₁, .elem 0,
        stepIter_chain (meval_deref_e_S ρ₀ σT (quoteD e) ρT κ)
          (stepIter_chain runE
            (mderef_cell_S ρ₀ σT₁ (quoteD e) ρT aT dT κ))⟩
  | @setLoc l e ρ σ σ₁ σ₂ n w _ _ ihl ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nl, vlT, σT₁, hF₁, repL, runL⟩ :=
      ihl ρ₀ hρ hF (setKl ρ₀ (quoteD l) (quoteD e) ρT κ)
    obtain rfl := locR_inv repL
    obtain ⟨nx, wTv, σT₂, hF₂, repW, runW⟩ :=
      ihe ρ₀ hρ hF₁ (setKx ρ₀ (quoteD l) (quoteD e) ρT
        (.cell (.elem 5) (.loc (14 + n))) κ)
    have hset : (knotStoreF ρ₀ ++ σT₂).set (14 + n) wTv =
        knotStoreF ρ₀ ++ σT₂.set n wTv := by
      have h := set_append_right' (knotStoreF ρ₀) σT₂ n wTv
      rwa [knot_length ρ₀] at h
    have run2 := stepIter_chain
      (meval_set_l_S ρ₀ σT (quoteD l) (quoteD e) ρT κ)
      (stepIter_chain runL
        (stepIter_chain
          (meval_set_x_S ρ₀ σT₁ (quoteD l) (quoteD e) ρT
            (.cell (.elem 5) (.loc (14 + n))) κ)
          (stepIter_chain runW
            (stepIter_chain
              (set_pre_S ρ₀ σT₂ (quoteD l) (quoteD e) ρT wTv
                (14 + n) κ)
              (stepIter_chain
                (set_fire (knotStoreF ρ₀ ++ σT₂) wTv (14 + n)
                  (setKp ρ₀ (quoteD l) (quoteD e) ρT wTv (14 + n) κ))
                (set_post_S ρ₀ ((knotStoreF ρ₀ ++ σT₂).set (14 + n) wTv)
                  (quoteD l) (quoteD e) ρT wTv (14 + n) κ))))))
    rw [hset] at run2
    exact ⟨188 + (nl + (23 + (nx + (68 + (1 + 2))))), wTv,
      σT₂.set n wTv, forall₂_set hF₂ repW, repW, run2⟩
  | @setErr l e ρ σ σ₁ σ₂ vl w _ hw _ ihl ihe =>
    intro ρ₀ ρT hρ σT hF κ
    obtain ⟨nl, vlT, σT₁, hF₁, repL, runL⟩ :=
      ihl ρ₀ hρ hF (setKl ρ₀ (quoteD l) (quoteD e) ρT κ)
    cases vl with
    | loc n => exact absurd rfl (hw n)
    | cont κ' => exact (kontR_inv repL).elim
    | elem k =>
      obtain rfl := elemR_inv repL
      obtain ⟨nx, wTv, σT₂, hF₂, repW, runW⟩ :=
        ihe ρ₀ hρ hF₁ (setKx ρ₀ (quoteD l) (quoteD e) ρT
          (.cell (.elem 2) (.elem k)) κ)
      exact ⟨188 + (nl + (23 + (nx + 57))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_set_l_S ρ₀ σT (quoteD l) (quoteD e) ρT κ)
          (stepIter_chain runL
            (stepIter_chain
              (meval_set_x_S ρ₀ σT₁ (quoteD l) (quoteD e) ρT
                (.cell (.elem 2) (.elem k)) κ)
              (stepIter_chain runW
                (mset_elem_S ρ₀ σT₂ (quoteD l) (quoteD e) ρT
                  wTv k κ))))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repL
      obtain ⟨nx, wTv, σT₂, hF₂, repW, runW⟩ :=
        ihe ρ₀ hρ hF₁ (setKx ρ₀ (quoteD l) (quoteD e) ρT
          (.cell (.elem 3) (.cell (quoteD b') ρTx)) κ)
      exact ⟨188 + (nl + (23 + (nx + 57))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_set_l_S ρ₀ σT (quoteD l) (quoteD e) ρT κ)
          (stepIter_chain runL
            (stepIter_chain
              (meval_set_x_S ρ₀ σT₁ (quoteD l) (quoteD e) ρT
                (.cell (.elem 3) (.cell (quoteD b') ρTx)) κ)
              (stepIter_chain runW
                (mset_clos_S ρ₀ σT₂ (quoteD l) (quoteD e) ρT
                  (quoteD b') ρTx wTv κ))))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repL
      obtain ⟨nx, wTv, σT₂, hF₂, repW, runW⟩ :=
        ihe ρ₀ hρ hF₁ (setKx ρ₀ (quoteD l) (quoteD e) ρT
          (.cell (.elem 6) (.cell aT dT)) κ)
      exact ⟨188 + (nl + (23 + (nx + 64))), _, σT₂, hF₂, .elem 0,
        stepIter_chain (meval_set_l_S ρ₀ σT (quoteD l) (quoteD e) ρT κ)
          (stepIter_chain runL
            (stepIter_chain
              (meval_set_x_S ρ₀ σT₁ (quoteD l) (quoteD e) ρT
                (.cell (.elem 6) (.cell aT dT)) κ)
              (stepIter_chain runW
                (mset_cell_S ρ₀ σT₂ (quoteD l) (quoteD e) ρT
                  aT dT wTv κ))))⟩

/-! ## Top-level adequacy for the 12-form fragment -/

/-- **Adequacy with live stores**: from one store-threading
    derivation of a closed program started at the empty store — the
    meta run converges, the direct run converges, the values stand
    in the relation, and the final stores are pointwise related. -/
theorem adequacy_store {p : Prog} {v : Val} {σ₂ : Store}
    (h : EvS p [] [] v σ₂) :
    ∃ (n : Nat) (vT : Val) (σT₂ : Store),
      List.Forall₂ (RepV 14 KRempty) σT₂ σ₂ ∧
      RepV 14 KRempty vT v ∧
      loop n (metaState p) = some vT ∧
      ∃ m, runM m [] [] p = some v := by
  obtain ⟨n, vT, σT₂, hF₂, rep, run⟩ :=
    meval_simS h [quoteD p] .nil List.Forall₂.nil .halt
  obtain ⟨m, hm⟩ := evS_steps h .halt
  have lastM : stepIter 1 (.ret vT (knotStoreF [quoteD p] ++ σT₂) .halt) =
      .inr vT := rfl
  have lastD : stepIter 1 (.ret v σ₂ .halt) = .inr v := rfl
  exact ⟨entrySteps + (17 + (n + 1)), vT, σT₂, hF₂, rep,
    loop_of_stepIter_inr
      (stepIter_chain (meval_entry p)
        (stepIter_chain (call_entry_S p) (stepIter_chain run lastM))),
    m + 1, loop_of_stepIter_inr (stepIter_chain hm lastD)⟩

/-! ## The store roundtrips, through the interpreter -/

/-- **Allocate then read**: `deref (ref (atom k))` — the value
    survives the store roundtrip in both worlds, for every element.
    An instance of the master theorem: no kernel reduction left. -/
theorem adequacy_ref_deref (k : Fin 8) :
    ∃ n, loop n (metaState (.deref (.ref (.atom k)))) =
      some (.cell (.elem 2) (.elem k)) ∧
    ∃ m, runM m [] [] (.deref (.ref (.atom k))) = some (.elem k) := by
  have h : EvS (.deref (.ref (.atom k))) [] [] (.elem k) [.elem k] :=
    EvS.derefLoc (EvS.ref (EvS.atom k [] [])) (by simp)
  obtain ⟨n, vT, σT₂, hF₂, rep, hloop, m, hrun⟩ := adequacy_store h
  obtain rfl := elemR_inv rep
  exact ⟨n, hloop, m, hrun⟩

/-- **Allocate then overwrite**: `setref (ref (atom j)) (atom k)` —
    the written value returns in both worlds, all 64 pairs. -/
theorem adequacy_setref (j k : Fin 8) :
    ∃ n, loop n (metaState (.setref (.ref (.atom j)) (.atom k))) =
      some (.cell (.elem 2) (.elem k)) ∧
    ∃ m, runM m [] [] (.setref (.ref (.atom j)) (.atom k)) =
      some (.elem k) := by
  have h : EvS (.setref (.ref (.atom j)) (.atom k)) [] []
      (.elem k) [.elem k] :=
    EvS.setLoc (EvS.ref (EvS.atom j [] [])) (EvS.atom k [] [.elem j])
  obtain ⟨n, vT, σT₂, hF₂, rep, hloop, m, hrun⟩ := adequacy_store h
  obtain rfl := elemR_inv rep
  exact ⟨n, hloop, m, hrun⟩

end AdequacyStore
end Dichotomic

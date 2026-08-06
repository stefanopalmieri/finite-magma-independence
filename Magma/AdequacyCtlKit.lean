import Magma.AdequacyStoreKit

/-!
# Adequacy campaign, rung 6 (kit): control — capture, throw, and
# continuations as values

The kernel-reduction half of rung 6. Nine dispatch lemmas:

* **`meval_callcc_S`** — the absorption, certified: 132 steps from
  the `callcc` quotation to the body's recursive call, with the
  captured host continuation **literally the base `κ`** of the
  calling convention (the `rfl` verifies the capture point is the
  tail), shf-tagged and consed onto the tagged environment — the
  machine's own `callcc` arm, one level up.
* **`mapply_shf_S`** — the throw: applying a shf-tagged continuation
  delivers the tagged argument *verbatim* to the captured
  continuation in 260 steps — value and target both passengers; the
  machine's cont-application arm, one level up.
* **Continuations as values** — now that `callcc` puts shf-tagged
  values into environments, every tag-dispatching arm meets them;
  all seven agree with the machine's treatment of `cont` values:
  `car`/`cdr`/`deref` default (57), `pairp` says no (57), `ite`
  takes the truthy then-branch (107), an element applied to one
  defaults (183), `setref` targeting one defaults (57). The
  error-arm agreement streak of the campaign remains unbroken.

Plus `eqvFreeB`, the executable check that the frozen image itself
is in the 13-form domain (`meta_eqvFree`) — the fact that lets the
rung-6 simulation apply to META's own runs, and with it the tower.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyCtlKit

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep
  AdequacyLeaf AdequacySim AdequacyData AdequacyStoreKit

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **The absorption**: `callcc` dispatch is a tail call into the
    body with the *base continuation itself* captured, shf-tagged,
    and consed onto the environment — exactly the machine's
    `callcc` arm, one level up. -/
theorem meval_callcc_S (ρ₀ : Env) (σ' : Store) (qb ρT : Val)
    (κ : Kont) :
    stepIter 132 (mevalCallS ρ₀ σ' (.cell (.elem 6) qb) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qb
        (.cell (.cell (.elem 4) (.cont κ)) ρT) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **The throw**: applying a shf-tagged continuation delivers the
    tagged argument verbatim to the captured continuation — the
    machine's cont-application arm, one level up. Value and target
    both passengers. -/
theorem mapply_shf_S (ρ₀ : Env) (σ' : Store) (qf qx ρT vxT : Val)
    (κt κ : Kont) :
    stepIter 260 (.ret vxT (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 4) (.cont κt)) κ)) =
      .inl (.ret vxT (knotStoreF ρ₀ ++ σ') κt) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **An element applied to a continuation**: default agreement. -/
theorem mapply_elem_shf_S (ρ₀ : Env) (σ' : Store) (qf qx ρT : Val)
    (a : Fin 8) (κt κ : Kont) :
    stepIter 183 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` of a continuation**: default agreement. -/
theorem mcar_shf_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (κt κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ') (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` of a continuation**: default agreement. -/
theorem mcdr_shf_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (κt κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ') (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` of a continuation**: no. -/
theorem mpairp_shf_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val)
    (κt κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ') (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` of a continuation**: default agreement. -/
theorem mderef_shf_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val)
    (κt κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ') (derefKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` on a continuation**: truthy — the then-branch, tail
    call (the machine's non-element arm). -/
theorem mite_shf_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT : Val)
    (κt κ : Kont) :
    stepIter 107 (.ret (.cell (.elem 4) (.cont κt))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qt ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref` targeting a continuation**: default agreement, store
    untouched. -/
theorem mset_shf_S (ρ₀ : Env) (σ' : Store) (ql qe ρT wT : Val)
    (κt κ : Kont) :
    stepIter 57 (.ret wT (knotStoreF ρ₀ ++ σ')
        (setKx ρ₀ ql qe ρT (.cell (.elem 4) (.cont κt)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

/-! ## The image is in the domain -/

/-- Executable eqv-freeness. -/
def eqvFreeB : Prog → Bool
  | .atom _ => true
  | .var _ => true
  | .lam b => eqvFreeB b
  | .app f x => eqvFreeB f && eqvFreeB x
  | .callcc b => eqvFreeB b
  | .ref e => eqvFreeB e
  | .deref e => eqvFreeB e
  | .setref l e => eqvFreeB l && eqvFreeB e
  | .cons a b => eqvFreeB a && eqvFreeB b
  | .car e => eqvFreeB e
  | .cdr e => eqvFreeB e
  | .pairp e => eqvFreeB e
  | .ite c t e => eqvFreeB c && (eqvFreeB t && eqvFreeB e)
  | .eqv _ _ => false

theorem eqvFree_of_eqvFreeB : ∀ p, eqvFreeB p = true → EqvFree p := by
  intro p
  induction p with
  | atom a => exact fun _ => trivial
  | var n => exact fun _ => trivial
  | lam b ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | app f x ihf ihx =>
    intro h
    simp only [eqvFreeB, Bool.and_eq_true] at h
    exact ⟨ihf h.1, ihx h.2⟩
  | callcc b ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | ref e ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | deref e ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | setref l e ihl ihe =>
    intro h
    simp only [eqvFreeB, Bool.and_eq_true] at h
    exact ⟨ihl h.1, ihe h.2⟩
  | cons a b iha ihb =>
    intro h
    simp only [eqvFreeB, Bool.and_eq_true] at h
    exact ⟨iha h.1, ihb h.2⟩
  | car e ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | cdr e ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | pairp e ih => exact fun h => ih (by simpa [eqvFreeB] using h)
  | ite c t e ihc iht ihe =>
    intro h
    simp only [eqvFreeB, Bool.and_eq_true] at h
    exact ⟨ihc h.1, iht h.2.1, ihe h.2.2⟩
  | eqv a b _ _ => intro h; simp [eqvFreeB] at h

/-- **The frozen image is in the 13-form domain**: META itself is
    eqv-free — the fact that lets the rung-6 simulation apply to
    META's own runs, and with it the tower. -/
theorem meta_eqvFree : EqvFree META :=
  eqvFree_of_eqvFreeB META (by native_decide)

end AdequacyCtlKit
end Dichotomic

import Magma.Dichotomic
import Magma.Witness5
import Magma.Witness6
import Magma.OneSidedSeparation
import Mathlib.Data.Fintype.Perm

/-!
# Role Rigidity

An extensional 2-pointed magma satisfying the D dichotomy has a canonical
role-class decomposition `S = Z ⊔ C ⊔ N` (Theorem `three_cat_decomposition` in
`Dichotomic.lean`). Role classes are isomorphism invariants
(`Functoriality.lean`). This file strengthens the class-level canonicity to
the individual-role level for the paper's main witnesses.

## Role rigidity

A magma is **role-rigid** when the only Cayley-table-preserving injection of
its carrier to itself is the identity — i.e., when its automorphism group is
trivial. In a role-rigid magma, each element is fixed by every automorphism,
so individual role assignments (which absorber is `z₁`, which core element is
the section `s`, which is the retraction `r`, which is the classifier `τ`,
etc.) are intrinsic algebraic invariants of the Cayley table, not artifacts
of presentation. In this sense, syntax fully determines semantics: there is
no presentation freedom beyond what the operation already fixes.

## Results

The paper's main witnesses are role-rigid:

  * `witness5_classifier_swap_aut` — N=5 R+D+H coexistence (`dotW5`)
    is non-rigid; the classifier transposition (2 3) is its non-trivial
    automorphism (and, by the mirror-row theorem, its *only* one).
  * `witness6_role_rigid`  — N=6 R+D+H coexistence (`dotW6`)
  * `kripke4_role_rigid`   — N=4 R+D (`dotK4`)
  * `kripke5_role_rigid`   — N=5 R+D with s ≠ r (`dotK5`)
  * `oss_role_rigid`       — N=4 one-sided separator (`dotOSS`)

Each is discharged by `decide` (or `native_decide` for N ≥ 6): the universe
of candidate injections `Fin n → Fin n` is finite, and all required predicates
are decidable.

## Polar vs symmetric absorbers

Corollary: in every role-rigid magma, the two absorbers lie in distinct
automorphism orbits — no permutation exchanges them. This is the algebraic
form of the "polar reading" of the absorber pair; the "symmetric reading"
(two indistinguishable absorbers) requires an absorber-swapping automorphism,
which role-rigidity rules out.
-/

set_option autoImplicit false

namespace Dichotomic

-- ══════════════════════════════════════════════════════════════════════
-- Role rigidity: definition
-- ══════════════════════════════════════════════════════════════════════

/-- A magma `(Fin n, dot)` is **role-rigid** if every operation-preserving
    bijection of its carrier to itself fixes every element. Equivalently,
    the automorphism group of the magma is trivial.

    We quantify over `Equiv.Perm (Fin n)` — the permutation group of `Fin n`
    — and express rigidity pointwise (`σ x = x` for all `x`) rather than as
    `σ = Equiv.refl _`, which simplifies decidability synthesis. -/
def IsRoleRigid (n : Nat) (dot : Fin n → Fin n → Fin n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    (∀ a b : Fin n, σ (dot a b) = dot (σ a) (σ b)) →
    ∀ x : Fin n, σ x = x

-- ══════════════════════════════════════════════════════════════════════
-- Main witnesses are role-rigid
-- ══════════════════════════════════════════════════════════════════════

/-- **The canonical N=5 coexistence witness `dotW5` is *not* role-rigid:
    it admits the classifier transposition (2 3) as a non-trivial
    automorphism.** This is by design — the canonical witness internalises
    its symmetry as g's action on core (g·τ₁ = τ₂, g·τ₂ = τ₁). The
    mirror-row theorem (`Magma/MirrorRow.lean`) ensures this is the only
    possible non-trivial automorphism: |Aut(dotW5)| = 2. -/
theorem witness5_classifier_swap_aut :
    ∀ a b : Fin 5, (Equiv.swap (2 : Fin 5) 3) (dotW5 a b)
      = dotW5 ((Equiv.swap (2 : Fin 5) 3) a) ((Equiv.swap (2 : Fin 5) 3) b) := by
  decide

/-- **The N=6 coexistence witness is role-rigid.** -/
theorem witness6_role_rigid : IsRoleRigid 6 dotW6 := by
  unfold IsRoleRigid; native_decide

/-- **The N=4 kripke FRM is role-rigid.** -/
theorem kripke4_role_rigid : IsRoleRigid 4 dotK4 := by
  unfold IsRoleRigid; native_decide

/-- **The N=5 kripke FRM (s ≠ r) is role-rigid.** -/
theorem kripke5_role_rigid : IsRoleRigid 5 dotK5 := by
  unfold IsRoleRigid; native_decide

/-- **The N=4 one-sided separator is role-rigid.** -/
theorem oss_role_rigid : IsRoleRigid 4 dotOSS := by
  unfold IsRoleRigid; native_decide

-- ══════════════════════════════════════════════════════════════════════
-- Polar absorber pair: corollary of role rigidity
-- ══════════════════════════════════════════════════════════════════════

/-- In a role-rigid magma with two distinct absorbers, no automorphism
    exchanges the absorbers. This is the algebraic form of the "polar
    reading" of the absorber pair: the two absorbers occupy distinct
    `Aut(M)`-orbits, and the symmetric reading (an involution swapping
    them) is ruled out. -/
theorem role_rigid_polar_absorbers
    {n : Nat} {dot : Fin n → Fin n → Fin n}
    (h_rigid : IsRoleRigid n dot)
    (z₁ z₂ : Fin n) (h_distinct : z₁ ≠ z₂)
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (dot a b) = dot (σ a) (σ b)) :
    σ z₁ ≠ z₂ := by
  intro h_swap
  have : σ z₁ = z₁ := h_rigid σ h_hom z₁
  exact h_distinct (this.symm.trans h_swap)

end Dichotomic

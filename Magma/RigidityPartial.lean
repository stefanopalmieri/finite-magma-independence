import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Basic

/-!
# Partial Role Rigidity from Unique Classifier with Asymmetric Profile

If a finite extensional 2-pointed magma has a **unique** classifier `τ` whose
`z₁`-preimage and `z₂`-preimage (on the full carrier) have different
cardinalities, then no automorphism swaps the two absorbers.

This is a "partial" rigidity result: it rules out absorber-swapping
automorphisms without requiring full role-rigidity (`Aut = 1`). It's strictly
easier to verify — uniqueness and a cardinality asymmetry can be checked from
the Cayley table without enumerating the automorphism group.

## Proof sketch

An automorphism `σ` with `σ z₁ = z₂` must send the unique classifier `τ` to
itself (automorphisms preserve "being a classifier" and `core`, and uniqueness
pins down the image). Applying `σ` to `dot τ x = z₁` yields
`dot τ (σ x) = z₂`, so `σ` bijects the `z₁`-preimage of `τ` onto the
`z₂`-preimage. Bijections preserve cardinality — contradicting the asymmetry.

## Note on signature

The signature matches the requested theorem, with one additional hypothesis
`h_no_other_zeros` reflecting the E2PM structure (the only left-absorbers are
`z₁, z₂`). Without this, `σ z₂` could in principle be a "third" absorber and
extensionality alone does not eliminate that possibility. This hypothesis is
already part of `Ext2PointedMagma` in `Magma/E2PM.lean`, so the theorem remains
directly applicable to any E2PM.
-/

set_option autoImplicit false

namespace KripkeWall

/-- **Unique Classifier with Asymmetric Profile ⇒ No Swap Automorphism.**

If an extensional 2-pointed magma has a unique classifier `τ` whose `z₁`- and
`z₂`-preimages on `Fin n` have different cardinalities, then no automorphism
`σ` satisfies `σ z₁ = z₂`. -/
theorem unique_classifier_asymmetric_profile_polar
    {n : Nat} (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n)
    (h_abs₁ : ∀ x, dot z₁ x = z₁)
    (h_abs₂ : ∀ x, dot z₂ x = z₂)
    (h_distinct : z₁ ≠ z₂)
    (h_ext : ∀ a b : Fin n, (∀ x, dot a x = dot b x) → a = b)
    (h_no_other_zeros : ∀ y : Fin n, (∀ x : Fin n, dot y x = y) → y = z₁ ∨ y = z₂)
    (τ : Fin n)
    (h_τ_core : τ ≠ z₁ ∧ τ ≠ z₂)
    (h_τ_cls : ∀ x, dot τ x = z₁ ∨ dot τ x = z₂)
    (h_τ_unique :
      ∀ y : Fin n, y ≠ z₁ → y ≠ z₂ →
        (∀ x, dot y x = z₁ ∨ dot y x = z₂) → y = τ)
    (h_asymmetric :
      (Finset.univ.filter (fun x => dot τ x = z₁)).card ≠
      (Finset.univ.filter (fun x => dot τ x = z₂)).card)
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b, σ (dot a b) = dot (σ a) (σ b))
    (h_swap : σ z₁ = z₂) :
    False := by
  -- Unused but kept for signature completeness: `h_ext` (extensionality) and
  -- `h_abs₁` (z₁ is a left-absorber). The proof uses `h_no_other_zeros` and
  -- `h_abs₂` (via σ z₂ being an absorber) to pin down the absorber swap.
  have _ := h_ext
  have _ := h_abs₁
  -- Step 1: σ z₂ is a left-absorber. For all x = σ y, we have
  -- dot (σ z₂) (σ y) = σ (dot z₂ y) = σ z₂. Since σ is surjective, this covers all x.
  have h_σz₂_abs : ∀ x : Fin n, dot (σ z₂) x = σ z₂ := by
    intro x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [← h_hom, h_abs₂]
  -- σ is injective, σ z₁ = z₂, and z₁ ≠ z₂, so σ z₂ ≠ z₂.
  have h_σz₂_ne_z₂ : σ z₂ ≠ z₂ := by
    intro h
    apply h_distinct
    apply σ.injective
    rw [h_swap, h]
  -- By h_no_other_zeros, σ z₂ = z₁ or σ z₂ = z₂; the latter is excluded.
  have h_swap₂ : σ z₂ = z₁ := by
    rcases h_no_other_zeros (σ z₂) h_σz₂_abs with h | h
    · exact h
    · exact (h_σz₂_ne_z₂ h).elim
  -- Step 2: σ τ is a classifier in core, hence σ τ = τ by uniqueness.
  -- σ τ ≠ z₁: σ τ = z₁ = σ z₂ ⇒ τ = z₂, contradiction.
  have h_στ_ne_z₁ : σ τ ≠ z₁ := by
    intro h
    apply h_τ_core.2
    apply σ.injective
    rw [h, h_swap₂]
  -- σ τ ≠ z₂: σ τ = z₂ = σ z₁ ⇒ τ = z₁, contradiction.
  have h_στ_ne_z₂ : σ τ ≠ z₂ := by
    intro h
    apply h_τ_core.1
    apply σ.injective
    rw [h, h_swap]
  -- σ τ is a classifier: for any x = σ y, dot (σ τ) (σ y) = σ (dot τ y) ∈ {σ z₁, σ z₂} = {z₂, z₁}.
  have h_στ_cls : ∀ x, dot (σ τ) x = z₁ ∨ dot (σ τ) x = z₂ := by
    intro x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [← h_hom]
    rcases h_τ_cls y with h | h
    · rw [h, h_swap]; right; rfl
    · rw [h, h_swap₂]; left; rfl
  -- Uniqueness: σ τ = τ.
  have h_στ_eq : σ τ = τ := h_τ_unique (σ τ) h_στ_ne_z₁ h_στ_ne_z₂ h_στ_cls
  -- Step 3: σ bijects {x : dot τ x = z₁} to {x : dot τ x = z₂}.
  -- The maps-to direction: if dot τ x = z₁ then dot τ (σ x) = z₂.
  -- Indeed, σ (dot τ x) = σ z₁ = z₂, and σ (dot τ x) = dot (σ τ) (σ x) = dot τ (σ x).
  set A : Finset (Fin n) := Finset.univ.filter (fun x => dot τ x = z₁) with hA
  set B : Finset (Fin n) := Finset.univ.filter (fun x => dot τ x = z₂) with hB
  -- σ(A) = B: the forward direction uses `dot τ x = z₁ ⇒ dot τ (σ x) = z₂`,
  -- the backward direction uses the same with σ replaced by σ⁻¹.
  have h_image_A : A.image σ = B := by
    ext x
    simp only [Finset.mem_image, A, B, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : dot (σ τ) (σ y) = dot τ (σ y) := by rw [h_στ_eq]
      rw [← this, ← h_hom, hy, h_swap]
    · intro hx
      refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
      -- dot τ (σ.symm x) = z₁.
      -- From dot τ x = z₂, substitute x = σ (σ.symm x):
      -- dot τ (σ (σ.symm x)) = z₂, i.e. dot (σ τ) (σ (σ.symm x)) = z₂ via h_στ_eq⁻¹,
      -- so σ (dot τ (σ.symm x)) = z₂ = σ z₁, hence dot τ (σ.symm x) = z₁ by σ injective.
      apply σ.injective
      rw [h_swap]
      -- Goal: σ (dot τ (σ.symm x)) = z₂.
      rw [h_hom, h_στ_eq, σ.apply_symm_apply]
      exact hx
  have h_card_eq : A.card = B.card := by
    rw [← h_image_A, Finset.card_image_of_injective _ σ.injective]
  exact h_asymmetric h_card_eq

end KripkeWall

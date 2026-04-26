/- # NoCommutativity — Self-Description Requires Asymmetry (and Two Absorbers)

   ## Statements

   1. No commutative magma can have two distinct left-absorbers.
   2. In an extensional magma with a left-absorber `z`, any element whose row
      is constantly `z` must equal `z` itself.

   The first result tells us that to admit two absorbers at all, the operation
   must be asymmetric. The second tells us why there must be two in the first
   place: with a single absorber, extensionality collapses any would-be
   classifier into the absorber, so the classifier dichotomy is unsatisfiable.
   Together these are the minimal-axiom obstructions that pin down the
   "extensional, 2-pointed" setting.

   In particular, neither the `FaithfulRetractMagma` nor `DichotomicRetractMagma`
   setups from `Dichotomic.lean` can be weakened to a commutative or
   single-absorber variant without collapse.

   ## Proofs

   **No-commutativity.** If `zero₁` and `zero₂` are distinct left-absorbers:
   - `dot zero₁ zero₂ = zero₁`  (zero₁ absorbs)
   - `dot zero₂ zero₁ = zero₂`  (zero₂ absorbs)
   - Commutativity: `dot zero₁ zero₂ = dot zero₂ zero₁`
   - Therefore `zero₁ = zero₂`, contradiction.

   **Single-absorber collapse.** The rows `x ↦ dot τ x` and `x ↦ dot z x`
   are both constantly `z`, so extensionality identifies `τ` and `z`.

   These are the simplest possible impossibilities: no dichotomy boundary, no
   retraction pair, no dichotomy. Just the absorber axioms — paired with
   commutativity in one case, extensionality in the other.
-/

import Magma.Dichotomic

set_option autoImplicit false

namespace Dichotomic

-- ══════════════════════════════════════════════════════════════════════
-- The No-Commutativity Theorem
-- ══════════════════════════════════════════════════════════════════════

section NoCommutativity

variable {n : Nat}

/-- **No commutativity with two absorbers**: if a magma has two distinct
    left-absorbers and is commutative, we get a contradiction.

    This is the weakest possible statement — it doesn't need extensionality,
    retraction pairs, or the classifier dichotomy. Just the two absorbers. -/
theorem no_comm_two_absorbers
    (dot : Fin n → Fin n → Fin n)
    (zero₁ zero₂ : Fin n)
    (h_abs₁ : ∀ x, dot zero₁ x = zero₁)
    (h_abs₂ : ∀ x, dot zero₂ x = zero₂)
    (h_distinct : zero₁ ≠ zero₂)
    (h_comm : ∀ a b, dot a b = dot b a) :
    False := by
  have h1 : dot zero₁ zero₂ = zero₁ := h_abs₁ zero₂
  have h2 : dot zero₂ zero₁ = zero₂ := h_abs₂ zero₁
  have h3 : dot zero₁ zero₂ = dot zero₂ zero₁ := h_comm zero₁ zero₂
  exact h_distinct (h1 ▸ h3 ▸ h2)

/-- **No commutative FaithfulRetractMagma**: commutativity is incompatible
    with the `FaithfulRetractMagma` axioms. -/
theorem FaithfulRetractMagma.no_commutativity (M : FaithfulRetractMagma n)
    (h_comm : ∀ a b : Fin n, M.dot a b = M.dot b a) :
    False :=
  no_comm_two_absorbers M.dot M.zero₁ M.zero₂
    M.zero₁_left M.zero₂_left M.zeros_distinct h_comm

/-- **No commutative DichotomicRetractMagma**: commutativity is incompatible
    with the `DichotomicRetractMagma` axioms. Immediate from the weaker result. -/
theorem DichotomicRetractMagma.no_commutativity (M : DichotomicRetractMagma n)
    (h_comm : ∀ a b : Fin n, M.dot a b = M.dot b a) :
    False :=
  M.toFaithfulRetractMagma.no_commutativity h_comm

end NoCommutativity

-- ══════════════════════════════════════════════════════════════════════
-- Single-Absorber Collapse
-- ══════════════════════════════════════════════════════════════════════

section SingleAbsorberCollapse

variable {n : Nat}

/-- **Single-absorber collapse**: in any extensional magma with a left-absorber
    `z`, any element whose row is constantly `z` equals `z`.

    This formalizes the minimality of the two-absorber axiom. The classifier
    condition in the dichotomy requires an element `τ` distinct from every
    absorber whose row lands in the absorber set. With a single absorber `z`,
    the condition `∀ x, dot τ x = z` makes `τ`'s row identical to `z`'s row,
    and extensionality forces `τ = z` — so no such `τ` exists. Two distinct
    absorbers is therefore the smallest count at which the dichotomy can be
    non-degenerately formulated.

    This uses only extensionality and one absorber — no retraction pair, no
    dichotomy, no commutativity hypothesis. It is the companion to
    `no_comm_two_absorbers`: one result says two absorbers force asymmetry,
    the other says one absorber forces classifier collapse. -/
theorem single_absorber_collapse
    (dot : Fin n → Fin n → Fin n)
    (z : Fin n)
    (h_abs : ∀ x, dot z x = z)
    (h_ext : ∀ a b : Fin n, (∀ x, dot a x = dot b x) → a = b)
    (τ : Fin n)
    (h_row : ∀ x, dot τ x = z) :
    τ = z :=
  h_ext τ z (fun x => (h_row x).trans (h_abs x).symm)

end SingleAbsorberCollapse

end Dichotomic

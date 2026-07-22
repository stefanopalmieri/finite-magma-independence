import Magma.Dichotomic
import Magma.ICP
import Magma.E2PM
import Magma.Witness5
import Magma.WitnessAllN

/-!
# Sorted Magmas: the First Connecting Axiom

The independence results show that S, D, and C never force one another:
any system in which the capabilities cohere does so by *additional*
axioms. This file identifies and studies the first such connecting
axiom: **sorting**.

## The axiom

Under D, every core element is a classifier (boolean on core) or a
non-classifier (core-valued on core). The dichotomy already makes
classifier rows compositional for free: a classifier's outputs on core
land in the absorbers, whose class is fixed. What D leaves open is the
*non-classifier* rows: for n a non-classifier and x core, the output
n ⬝ x is core, but its class (classifier or not) may depend arbitrarily
on both n and x. **Sorting** closes exactly this gap:

> the class of `n ⬝ x` depends only on the class of `x` — uniformly in
> the non-classifier `n` and the representative `x`.

A sorted dichotomic magma is thus "half a type system made whole": the
class map becomes compositional on core, i.e. a homomorphism-like
abstraction of the operation onto the classes — which is what a type
discipline is, algebraically.

## Results

- `sorted_involution` (algebraic, all n, one-sided retraction only):
  in a sorted magma with a classifier, a non-classifier, and a
  retraction pair whose members are non-classifiers (automatic by the
  placement theorem), the induced class-action of the non-classifiers
  is an **involution**: either every non-classifier preserves classes,
  or every non-classifier swaps them. S entangles with sorted D: of the
  four conceivable class-tables, only two survive. This is the first
  genuine interaction theorem between the capabilities — visible only
  after the connecting axiom is added.

- `witness5_sorted`: the canonical N=5 coexistence witness is sorted,
  in the class-preserving world.

- `unsorted5_*`: an N=5 S+D+C magma that is **not** sorted (its unique
  non-classifier acts as the transposition (τ₁ b), sending the two
  classifiers to different classes). Sorting is therefore a genuinely
  independent axiom — not implied by S+D+C even at the minimal
  coexistence size, where everything else is forced.

- `swap6_*`: an N=6 S+D+C magma that is sorted in the **class-swapping**
  world (the retraction pair exchanges the classifier block {4,5} with
  the non-classifier block {2,3}). Both worlds permitted by the
  involution theorem are inhabited. The swap world requires the section
  to inject the classifiers into the non-classifiers, hence |N| ≥ |C|;
  at N=5 the structure theorem forces |C| = 2, |N| = 1, so the swap
  world first appears at N=6 — one more face of the N=5 → N=6 phase
  transition.

Progressive rigidification: D alone sorts the classifier rows; sorting
makes the class map compositional; adding S cuts the sorted worlds from
four to two (involution); at N=5, cardinality cuts them to one
(class-preserving).
-/

set_option autoImplicit false

namespace Dichotomic

-- ═══════════════════════════════════════════════════════════════════
-- Class predicates and the sorting axiom
-- ═══════════════════════════════════════════════════════════════════

/-- `y` is on the classifier side: boolean on the core (disjunction form
    for decidability). -/
@[reducible] def ClsSide (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (y : Fin n) : Prop :=
  ∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot y x = z₁ ∨ dot y x = z₂)

/-- `y` is on the non-classifier side: core-valued on the core. -/
@[reducible] def NclSide (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (y : Fin n) : Prop :=
  ∀ x : Fin n, x = z₁ ∨ x = z₂ ∨ (dot y x ≠ z₁ ∧ dot y x ≠ z₂)

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ y : Fin n) :
    Decidable (ClsSide n dot z₁ z₂ y) :=
  Fintype.decidableForallFintype

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ y : Fin n) :
    Decidable (NclSide n dot z₁ z₂ y) :=
  Fintype.decidableForallFintype

/-- **The sorting axiom**: the class of `y ⬝ x` depends only on the
    class of `x`, uniformly in the acting non-classifier `y` and in the
    representative `x`. Equivalently: the Z/C/N decomposition is
    compositional on the core — a type discipline. -/
@[reducible] def Sorted (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) : Prop :=
  ∀ y y' x x' : Fin n,
    y ≠ z₁ → y ≠ z₂ → y' ≠ z₁ → y' ≠ z₂ →
    x ≠ z₁ → x ≠ z₂ → x' ≠ z₁ → x' ≠ z₂ →
    NclSide n dot z₁ z₂ y → NclSide n dot z₁ z₂ y' →
    (ClsSide n dot z₁ z₂ x ↔ ClsSide n dot z₁ z₂ x') →
    (ClsSide n dot z₁ z₂ (dot y x) ↔ ClsSide n dot z₁ z₂ (dot y' x'))

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) :
    Decidable (Sorted n dot z₁ z₂) :=
  Fintype.decidableForallFintype

/-- Every non-classifier preserves the classes. -/
@[reducible] def ClassPreserving (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : Prop :=
  ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
    NclSide n dot z₁ z₂ y →
    (ClsSide n dot z₁ z₂ x → ClsSide n dot z₁ z₂ (dot y x)) ∧
    (NclSide n dot z₁ z₂ x → NclSide n dot z₁ z₂ (dot y x))

/-- Every non-classifier swaps the classes. -/
@[reducible] def ClassSwapping (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : Prop :=
  ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
    NclSide n dot z₁ z₂ y →
    (ClsSide n dot z₁ z₂ x → NclSide n dot z₁ z₂ (dot y x)) ∧
    (NclSide n dot z₁ z₂ x → ClsSide n dot z₁ z₂ (dot y x))

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) :
    Decidable (ClassPreserving n dot z₁ z₂) :=
  Fintype.decidableForallFintype

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) :
    Decidable (ClassSwapping n dot z₁ z₂) :=
  Fintype.decidableForallFintype

-- ═══════════════════════════════════════════════════════════════════
-- The involution theorem: S entangles with sorted D
-- ═══════════════════════════════════════════════════════════════════

/-- **Sorted involution.** In a sorted dichotomic magma with a classifier
    τ, a non-classifier n₀, and a one-sided retraction pair (s, r) whose
    members are non-classifiers (automatic under D by the placement
    theorem), the class-action of the non-classifiers is an involution:
    either every non-classifier preserves both classes, or every
    non-classifier swaps them. Of the four conceivable class-tables,
    S leaves only two. Pure equational reasoning, uniform in n. -/
theorem sorted_involution (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (n₀ : Fin n) (hn1 : n₀ ≠ z₁) (hn2 : n₀ ≠ z₂) (hn₀N : NclSide n dot z₁ z₂ n₀)
    (s r : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hr1 : r ≠ z₁) (hr2 : r ≠ z₂)
    (hsN : NclSide n dot z₁ z₂ s) (hrN : NclSide n dot z₁ z₂ r)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x)
    (hsort : Sorted n dot z₁ z₂) :
    ClassPreserving n dot z₁ z₂ ∨ ClassSwapping n dot z₁ z₂ := by
  -- a non-classifier is never on the classifier side (witnessed at τ)
  have hNC : ∀ t : Fin n, NclSide n dot z₁ z₂ t → ¬ ClsSide n dot z₁ z₂ t := by
    intro t htN htC
    rcases htC τ with h | h | h
    · exact hτ1 h
    · exact hτ2 h
    · rcases (htN τ).resolve_left hτ1 |>.resolve_left hτ2 with ⟨h1, h2⟩
      rcases h with h' | h'
      · exact h1 h'
      · exact h2 h'
  -- a core element that is not on the classifier side is a non-classifier
  have hDN : ∀ t : Fin n, t ≠ z₁ → t ≠ z₂ → ¬ ClsSide n dot z₁ z₂ t →
      NclSide n dot z₁ z₂ t := by
    intro t ht1 ht2 htC
    rcases hdich t with h | h | h | h
    · exact absurd h ht1
    · exact absurd h ht2
    · exact absurd h htC
    · exact h
  have hn₀notC : ¬ ClsSide n dot z₁ z₂ n₀ := hNC n₀ hn₀N
  -- core-ness of the section's images
  have hsτ : dot s τ ≠ z₁ ∧ dot s τ ≠ z₂ :=
    ((hsN τ).resolve_left hτ1).resolve_left hτ2
  have hsn₀ : dot s n₀ ≠ z₁ ∧ dot s n₀ ≠ z₂ :=
    ((hsN n₀).resolve_left hn1).resolve_left hn2
  by_cases hP : ClsSide n dot z₁ z₂ (dot s τ)
  · -- class-preserving world
    left
    -- s sends the non-classifier n₀ to the non-classifier class
    have hQ : ¬ ClsSide n dot z₁ z₂ (dot s n₀) := by
      intro hQ
      have h := hsort r s (dot s n₀) τ hr1 hr2 hs1 hs2
        hsn₀.1 hsn₀.2 hτ1 hτ2 hrN hsN ⟨fun _ => hτC, fun _ => hQ⟩
      rw [hrs n₀ hn1 hn2] at h
      exact hn₀notC (h.mpr hP)
    intro y x hy1 hy2 hx1 hx2 hyN
    have hout : dot y x ≠ z₁ ∧ dot y x ≠ z₂ :=
      ((hyN x).resolve_left hx1).resolve_left hx2
    constructor
    · intro hxC
      have h := hsort y s x τ hy1 hy2 hs1 hs2 hx1 hx2 hτ1 hτ2 hyN hsN
        ⟨fun _ => hτC, fun _ => hxC⟩
      exact h.mpr hP
    · intro hxN
      refine hDN _ hout.1 hout.2 ?_
      intro houtC
      have h := hsort y s x n₀ hy1 hy2 hs1 hs2 hx1 hx2 hn1 hn2 hyN hsN
        ⟨fun h' => absurd h' (hNC x hxN), fun h' => absurd h' hn₀notC⟩
      exact hQ (h.mp houtC)
  · -- class-swapping world
    right
    -- s sends the non-classifier n₀ to the classifier class
    have hR : ClsSide n dot z₁ z₂ (dot s n₀) := by
      by_contra hR
      have h := hsort r r (dot s τ) (dot s n₀) hr1 hr2 hr1 hr2
        hsτ.1 hsτ.2 hsn₀.1 hsn₀.2 hrN hrN
        ⟨fun h' => absurd h' hP, fun h' => absurd h' hR⟩
      rw [hrs τ hτ1 hτ2, hrs n₀ hn1 hn2] at h
      exact hn₀notC (h.mp hτC)
    intro y x hy1 hy2 hx1 hx2 hyN
    have hout : dot y x ≠ z₁ ∧ dot y x ≠ z₂ :=
      ((hyN x).resolve_left hx1).resolve_left hx2
    constructor
    · intro hxC
      refine hDN _ hout.1 hout.2 ?_
      intro houtC
      have h := hsort y s x τ hy1 hy2 hs1 hs2 hx1 hx2 hτ1 hτ2 hyN hsN
        ⟨fun _ => hτC, fun _ => hxC⟩
      exact hP (h.mp houtC)
    · intro hxN
      have h := hsort y s x n₀ hy1 hy2 hs1 hs2 hx1 hx2 hn1 hn2 hyN hsN
        ⟨fun h' => absurd h' (hNC x hxN), fun h' => absurd h' hn₀notC⟩
      exact h.mpr hR

-- ═══════════════════════════════════════════════════════════════════
-- The canonical witness is sorted (class-preserving world)
-- ═══════════════════════════════════════════════════════════════════

/-- The canonical N=5 S+D+C witness is sorted, in the class-preserving
    world: its unique non-classifier (the identity element 2) preserves
    both classes. -/
theorem witness5_sorted : Sorted 5 dotW5 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Sorting is independent: an unsorted S+D+C magma at N=5
-- ═══════════════════════════════════════════════════════════════════

/-! ```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 2, 3, 2, 4]   ← sec=ret (involution (2 3) on core, non-classifier)
  3 [0, 0, 1, 0, 0]   ← classifier (ICP a)
  4 [0, 1, 0, 1, 0]   ← classifier (ICP c)
```
The unique non-classifier 2 acts on the core as the transposition
(2 3): it sends the classifier 3 to the non-classifier 2, but the
classifier 4 to the classifier 4 — same input class, different output
classes. All of S, D, C hold, yet sorting fails. -/

private def rawU5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 3 | 2, 3 => 2 | 2, 4 => 4
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 0 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 0 | 4, 3 => 1 | 4, 4 => 0
  | _, _ => 0

private theorem rawU5_bound (a b : Fin 5) : rawU5 a.val b.val < 5 := by
  revert a b; decide

def dotU5 (a b : Fin 5) : Fin 5 := ⟨rawU5 a.val b.val, rawU5_bound a b⟩

/-- The unsorted witness is a full FaithfulRetractMagma (sec = ret = 2). -/
def unsorted5_frm : FaithfulRetractMagma 5 where
  dot := dotU5
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 2
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

theorem unsorted5_has_retract : HasRetractPair 5 dotU5 0 1 := by decide
theorem unsorted5_has_dichotomy : HasDichotomy 5 dotU5 0 1 := by decide
theorem unsorted5_has_icp : HasICP 5 dotU5 0 1 := by decide

/-- Sorting fails: 2 ⬝ 3 = 2 is a non-classifier while 2 ⬝ 4 = 4 is a
    classifier, though 3 and 4 share a class. -/
theorem unsorted5_not_sorted : ¬ Sorted 5 dotU5 0 1 := by decide

/-- **Sorting is a genuinely independent axiom**: it is not implied by
    S+D+C even at the minimal coexistence size N=5, where the role
    assignment is otherwise completely forced. -/
theorem sorting_independent :
    ∃ (_ : FaithfulRetractMagma 5),
      HasRetractPair 5 dotU5 0 1 ∧ HasDichotomy 5 dotU5 0 1 ∧
      HasICP 5 dotU5 0 1 ∧ ¬ Sorted 5 dotU5 0 1 :=
  ⟨unsorted5_frm, unsorted5_has_retract, unsorted5_has_dichotomy,
    unsorted5_has_icp, unsorted5_not_sorted⟩

-- ═══════════════════════════════════════════════════════════════════
-- The class-swapping world is inhabited: N=6
-- ═══════════════════════════════════════════════════════════════════

/-! ```
     0  1  2  3  4  5
  0 [0, 0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 2, 4, 5, 2, 3]   ← sec (pairing (2 4)(3 5): swaps N and C blocks)
  3 [0, 3, 4, 5, 2, 3]   ← ret (same core action, distinct absorber column)
  4 [0, 0, 1, 0, 0, 0]   ← classifier (ICP a)
  5 [0, 1, 0, 0, 1, 0]   ← classifier (ICP c)
```
Both non-classifiers send classifiers to non-classifiers and vice versa:
the sorted class-action is the swap. The section literally encodes the
classifier block inside the non-classifier block and back. -/

private def rawSw6 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 4 | 2, 3 => 5 | 2, 4 => 2 | 2, 5 => 3
  | 3, 0 => 0 | 3, 1 => 3 | 3, 2 => 4 | 3, 3 => 5 | 3, 4 => 2 | 3, 5 => 3
  | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 1 | 4, 3 => 0 | 4, 4 => 0 | 4, 5 => 0
  | 5, 0 => 0 | 5, 1 => 1 | 5, 2 => 0 | 5, 3 => 0 | 5, 4 => 1 | 5, 5 => 0
  | _, _ => 0

private theorem rawSw6_bound (a b : Fin 6) : rawSw6 a.val b.val < 6 := by
  revert a b; decide

def dotSw6 (a b : Fin 6) : Fin 6 := ⟨rawSw6 a.val b.val, rawSw6_bound a b⟩

/-- The swap-world witness is a full FaithfulRetractMagma with a
    non-degenerate retraction pair (sec = 2 ≠ 3 = ret). -/
def swap6_frm : FaithfulRetractMagma 6 where
  dot := dotSw6
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 3
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

theorem swap6_has_retract : HasRetractPair 6 dotSw6 0 1 := by decide
theorem swap6_has_dichotomy : HasDichotomy 6 dotSw6 0 1 := by decide
theorem swap6_has_icp : HasICP 6 dotSw6 0 1 := by decide
theorem swap6_sorted : Sorted 6 dotSw6 0 1 := by decide

/-- The swap world is realized: every non-classifier of `swap6` swaps
    the classes. -/
theorem swap6_swaps : ClassSwapping 6 dotSw6 0 1 := by decide

/-- The canonical witness lives in the other world: every non-classifier
    of `witness5` preserves the classes. -/
theorem witness5_class_preserving : ClassPreserving 5 dotW5 0 1 := by decide

/-- **Both sorted worlds are inhabited**: the class-preserving world at
    N=5 (`witness5_sorted`) and the class-swapping world at N=6
    (`swap6_sorted`, `swap6_swaps`) — with full S+D+C in both. The swap
    world cannot exist at N=5: the section must inject the classifiers
    into the non-classifiers, so |N| ≥ |C|, while the N=5 structure
    theorem forces |C| = 2, |N| = 1. -/
theorem swap_world_inhabited :
    ∃ (_ : FaithfulRetractMagma 6),
      HasRetractPair 6 dotSw6 0 1 ∧ HasDichotomy 6 dotSw6 0 1 ∧
      HasICP 6 dotSw6 0 1 ∧ Sorted 6 dotSw6 0 1 :=
  ⟨swap6_frm, swap6_has_retract, swap6_has_dichotomy,
    swap6_has_icp, swap6_sorted⟩

-- ═══════════════════════════════════════════════════════════════════
-- The four class-tables: complete classification
-- ═══════════════════════════════════════════════════════════════════

/-- Every non-classifier sends both classes to the classifier side. -/
@[reducible] def ClassConstC (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : Prop :=
  ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
    NclSide n dot z₁ z₂ y → ClsSide n dot z₁ z₂ (dot y x)

/-- Every non-classifier sends both classes to the non-classifier side. -/
@[reducible] def ClassConstN (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) : Prop :=
  ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
    NclSide n dot z₁ z₂ y → NclSide n dot z₁ z₂ (dot y x)

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) :
    Decidable (ClassConstC n dot z₁ z₂) :=
  Fintype.decidableForallFintype

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) :
    Decidable (ClassConstN n dot z₁ z₂) :=
  Fintype.decidableForallFintype

/-- **The constant class-tables force ¬S** (corollary of the involution
    theorem): a sorted magma in the const-C world admits no retraction
    pair with non-classifier members — and by the placement theorem all
    retraction pairs have non-classifier members. -/
theorem constC_blocks_retraction (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (n₀ : Fin n) (hn1 : n₀ ≠ z₁) (hn2 : n₀ ≠ z₂) (hn₀N : NclSide n dot z₁ z₂ n₀)
    (hsort : Sorted n dot z₁ z₂) (hconst : ClassConstC n dot z₁ z₂) :
    ¬ ∃ s r : Fin n, s ≠ z₁ ∧ s ≠ z₂ ∧ r ≠ z₁ ∧ r ≠ z₂ ∧
      NclSide n dot z₁ z₂ s ∧ NclSide n dot z₁ z₂ r ∧
      (∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x) := by
  rintro ⟨s, r, hs1, hs2, hr1, hr2, hsN, hrN, hrs⟩
  have hdisj : ∀ t : Fin n, ClsSide n dot z₁ z₂ t → NclSide n dot z₁ z₂ t → False := by
    intro t hC hN
    rcases hC τ with h | h | h
    · exact hτ1 h
    · exact hτ2 h
    · rcases (hN τ).resolve_left hτ1 |>.resolve_left hτ2 with ⟨h1, h2⟩
      rcases h with h' | h'
      · exact h1 h'
      · exact h2 h'
  rcases sorted_involution n dot z₁ z₂ hdich τ hτ1 hτ2 hτC n₀ hn1 hn2 hn₀N
    s r hs1 hs2 hr1 hr2 hsN hrN hrs hsort with hPres | hSwap
  · -- const-C contradicts preservation at the N-input n₀
    exact hdisj _ (hconst n₀ n₀ hn1 hn2 hn1 hn2 hn₀N)
      ((hPres n₀ n₀ hn1 hn2 hn1 hn2 hn₀N).2 hn₀N)
  · -- const-C contradicts swapping at the C-input τ
    exact hdisj _ (hconst n₀ τ hn1 hn2 hτ1 hτ2 hn₀N)
      ((hSwap n₀ τ hn1 hn2 hτ1 hτ2 hn₀N).1 hτC)

/-- Dual: the const-N world also forces ¬S. -/
theorem constN_blocks_retraction (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (n₀ : Fin n) (hn1 : n₀ ≠ z₁) (hn2 : n₀ ≠ z₂) (hn₀N : NclSide n dot z₁ z₂ n₀)
    (hsort : Sorted n dot z₁ z₂) (hconst : ClassConstN n dot z₁ z₂) :
    ¬ ∃ s r : Fin n, s ≠ z₁ ∧ s ≠ z₂ ∧ r ≠ z₁ ∧ r ≠ z₂ ∧
      NclSide n dot z₁ z₂ s ∧ NclSide n dot z₁ z₂ r ∧
      (∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x) := by
  rintro ⟨s, r, hs1, hs2, hr1, hr2, hsN, hrN, hrs⟩
  have hdisj : ∀ t : Fin n, ClsSide n dot z₁ z₂ t → NclSide n dot z₁ z₂ t → False := by
    intro t hC hN
    rcases hC τ with h | h | h
    · exact hτ1 h
    · exact hτ2 h
    · rcases (hN τ).resolve_left hτ1 |>.resolve_left hτ2 with ⟨h1, h2⟩
      rcases h with h' | h'
      · exact h1 h'
      · exact h2 h'
  rcases sorted_involution n dot z₁ z₂ hdich τ hτ1 hτ2 hτC n₀ hn1 hn2 hn₀N
    s r hs1 hs2 hr1 hr2 hsN hrN hrs hsort with hPres | hSwap
  · -- const-N contradicts preservation at the C-input τ
    exact hdisj _ ((hPres n₀ τ hn1 hn2 hτ1 hτ2 hn₀N).1 hτC)
      (hconst n₀ τ hn1 hn2 hτ1 hτ2 hn₀N)
  · -- const-N contradicts swapping at the N-input n₀
    exact hdisj _ ((hSwap n₀ n₀ hn1 hn2 hn1 hn2 hn₀N).2 hn₀N)
      (hconst n₀ n₀ hn1 hn2 hn1 hn2 hn₀N)

/-! The const-C world is realized by the existing tight D ⇏ S witness
`dNoS4_e2pm` (its unique non-classifier sends everything to the
classifier), and the const-N world by the table below. Both are
S-free — as the corollaries above force. Together with `witness5`
(preserving) and `swap6` (swapping), **all four class-tables are
realized, and S permits exactly the two involutive ones.** -/

theorem dNoS4_sorted : Sorted 4 dotDnoS4 0 1 := by decide
theorem dNoS4_constC : ClassConstC 4 dotDnoS4 0 1 := by decide

private def rawCN4 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 1 | 2, 3 => 1
  | 3, 0 => 0 | 3, 1 => 3 | 3, 2 => 3 | 3, 3 => 3
  | _, _ => 0

private theorem rawCN4_bound (a b : Fin 4) : rawCN4 a.val b.val < 4 := by
  revert a b; decide

def dotCN4 (a b : Fin 4) : Fin 4 := ⟨rawCN4 a.val b.val, rawCN4_bound a b⟩

def constN4_e2pm : Ext2PointedMagma 4 where
  dot := dotCN4
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

theorem constN4_has_dichotomy : HasDichotomy 4 dotCN4 0 1 := by decide
theorem constN4_sorted : Sorted 4 dotCN4 0 1 := by decide
theorem constN4_constN : ClassConstN 4 dotCN4 0 1 := by decide
theorem constN4_no_retract : ¬ HasRetractPair 4 dotCN4 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- The balance obstruction: the swap world needs |C| = |N|
-- ═══════════════════════════════════════════════════════════════════

/-- **Swap balance.** In the class-swapping world, a retraction pair
    (non-classifier members, one-sided equation only) forces exactly as
    many classifiers as non-classifiers: the section injects each class
    into the other. Under D the core is partitioned by the two classes,
    so the core has even size — in particular, within S+D+C the swap
    world can exist only at even N, and N=6 (`swap6`) is its minimum. -/
theorem swap_balance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hswap : ClassSwapping n dot z₁ z₂)
    (s r : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂)
    (hsN : NclSide n dot z₁ z₂ s)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x) :
    (Finset.univ.filter (fun y : Fin n =>
      y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y)).card =
    (Finset.univ.filter (fun y : Fin n =>
      y ≠ z₁ ∧ y ≠ z₂ ∧ NclSide n dot z₁ z₂ y)).card := by
  set Cset := Finset.univ.filter (fun y : Fin n =>
    y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y) with hCdef
  set Nset := Finset.univ.filter (fun y : Fin n =>
    y ≠ z₁ ∧ y ≠ z₂ ∧ NclSide n dot z₁ z₂ y) with hNdef
  have hmemC : ∀ y, y ∈ Cset ↔ y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y := by
    intro y
    simp [hCdef]
  have hmemN : ∀ y, y ∈ Nset ↔ y ≠ z₁ ∧ y ≠ z₂ ∧ NclSide n dot z₁ z₂ y := by
    intro y
    simp [hNdef]
  -- the section is injective on the core
  have hinj : ∀ x x' : Fin n, x ≠ z₁ → x ≠ z₂ → x' ≠ z₁ → x' ≠ z₂ →
      dot s x = dot s x' → x = x' := by
    intro x x' hx1 hx2 hx1' hx2' h
    have h1 := hrs x hx1 hx2
    rw [h, hrs x' hx1' hx2'] at h1
    exact h1.symm
  have h1 : Cset.card ≤ Nset.card := by
    apply Finset.card_le_card_of_injOn (fun y => dot s y)
    · intro y hy
      rcases (hmemC y).mp hy with ⟨hy1, hy2, hyC⟩
      have hcore := ((hsN y).resolve_left hy1).resolve_left hy2
      exact (hmemN _).mpr ⟨hcore.1, hcore.2,
        (hswap s y hs1 hs2 hy1 hy2 hsN).1 hyC⟩
    · intro x hx x' hx' h
      rcases (hmemC x).mp hx with ⟨hx1, hx2, -⟩
      rcases (hmemC x').mp hx' with ⟨hx1', hx2', -⟩
      exact hinj x x' hx1 hx2 hx1' hx2' h
  have h2 : Nset.card ≤ Cset.card := by
    apply Finset.card_le_card_of_injOn (fun y => dot s y)
    · intro y hy
      rcases (hmemN y).mp hy with ⟨hy1, hy2, hyN⟩
      have hcore := ((hsN y).resolve_left hy1).resolve_left hy2
      exact (hmemC _).mpr ⟨hcore.1, hcore.2,
        (hswap s y hs1 hs2 hy1 hy2 hsN).2 hyN⟩
    · intro x hx x' hx' h
      rcases (hmemN x).mp hx with ⟨hx1, hx2, -⟩
      rcases (hmemN x').mp hx' with ⟨hx1', hx2', -⟩
      exact hinj x x' hx1 hx2 hx1' hx2' h
  omega

/-- Under D the two classes partition the core, so swap balance makes the
    core even: |C| + |N| = 2 |C|. -/
theorem swap_even_core (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hswap : ClassSwapping n dot z₁ z₂)
    (s r : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂)
    (hsN : NclSide n dot z₁ z₂ s)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x) :
    ∃ k : Nat,
      (Finset.univ.filter (fun y : Fin n =>
        y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y)).card +
      (Finset.univ.filter (fun y : Fin n =>
        y ≠ z₁ ∧ y ≠ z₂ ∧ NclSide n dot z₁ z₂ y)).card = 2 * k := by
  have h := swap_balance n dot z₁ z₂ hswap s r hs1 hs2 hsN hrs
  exact ⟨(Finset.univ.filter (fun y : Fin n =>
    y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y)).card, by omega⟩

-- ═══════════════════════════════════════════════════════════════════
-- The class-preserving world exists at every N ≥ 5
-- ═══════════════════════════════════════════════════════════════════

private theorem fin_ne' {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)

/-- A class action determines sortedness: preserving implies Sorted. -/
theorem sorted_of_preserving (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (_hτC : ClsSide n dot z₁ z₂ τ)
    (hpres : ClassPreserving n dot z₁ z₂) :
    Sorted n dot z₁ z₂ := by
  have hdisj : ∀ t : Fin n, ClsSide n dot z₁ z₂ t → NclSide n dot z₁ z₂ t → False := by
    intro t hC hN
    rcases hC τ with h | h | h
    · exact hτ1 h
    · exact hτ2 h
    · rcases (hN τ).resolve_left hτ1 |>.resolve_left hτ2 with ⟨h1, h2⟩
      rcases h with h' | h'
      · exact h1 h'
      · exact h2 h'
  have key : ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
      NclSide n dot z₁ z₂ y →
      (ClsSide n dot z₁ z₂ (dot y x) ↔ ClsSide n dot z₁ z₂ x) := by
    intro y x hy1 hy2 hx1 hx2 hyN
    constructor
    · intro houtC
      by_contra hxC
      have hxN : NclSide n dot z₁ z₂ x := by
        rcases hdich x with h | h | h | h
        · exact absurd h hx1
        · exact absurd h hx2
        · exact absurd h hxC
        · exact h
      exact hdisj _ houtC ((hpres y x hy1 hy2 hx1 hx2 hyN).2 hxN)
    · exact (hpres y x hy1 hy2 hx1 hx2 hyN).1
  intro y y' x x' hy1 hy2 hy1' hy2' hx1 hx2 hx1' hx2' hyN hy'N hiff
  exact (key y x hy1 hy2 hx1 hx2 hyN).trans
    (hiff.trans (key y' x' hy1' hy2' hx1' hx2' hy'N).symm)

/-- Dual: swapping implies Sorted. -/
theorem sorted_of_swapping (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (_hτC : ClsSide n dot z₁ z₂ τ)
    (hswap : ClassSwapping n dot z₁ z₂) :
    Sorted n dot z₁ z₂ := by
  have hdisj : ∀ t : Fin n, ClsSide n dot z₁ z₂ t → NclSide n dot z₁ z₂ t → False := by
    intro t hC hN
    rcases hC τ with h | h | h
    · exact hτ1 h
    · exact hτ2 h
    · rcases (hN τ).resolve_left hτ1 |>.resolve_left hτ2 with ⟨h1, h2⟩
      rcases h with h' | h'
      · exact h1 h'
      · exact h2 h'
  have key : ∀ y x : Fin n, y ≠ z₁ → y ≠ z₂ → x ≠ z₁ → x ≠ z₂ →
      NclSide n dot z₁ z₂ y →
      (ClsSide n dot z₁ z₂ (dot y x) ↔ ¬ ClsSide n dot z₁ z₂ x) := by
    intro y x hy1 hy2 hx1 hx2 hyN
    constructor
    · intro houtC hxC
      exact hdisj _ houtC ((hswap y x hy1 hy2 hx1 hx2 hyN).1 hxC)
    · intro hnxC
      have hxN : NclSide n dot z₁ z₂ x := by
        rcases hdich x with h | h | h | h
        · exact absurd h hx1
        · exact absurd h hx2
        · exact absurd h hnxC
        · exact h
      exact (hswap y x hy1 hy2 hx1 hx2 hyN).2 hxN
  intro y y' x x' hy1 hy2 hy1' hy2' hx1 hx2 hx1' hx2' hyN hy'N hiff
  exact (key y x hy1 hy2 hx1 hx2 hyN).trans
    ((not_congr hiff).trans (key y' x' hy1' hy2' hx1' hx2' hy'N).symm)

/-- **The canonical scaling family is class-preserving at every N ≥ 5.**
    The non-classifiers of `dotN` (the identity element 2 and the
    swapped-identity elements k ≥ 5) all preserve both classes. -/
theorem witnessAllN_class_preserving (N : Nat) (h5 : 5 ≤ N) :
    ClassPreserving N (dotN N h5) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  intro y x hy1 hy2 hx1 hx2 hyN
  have hyv1 : y.val ≠ 0 := fun h => hy1 (Fin.ext h)
  have hyv2 : y.val ≠ 1 := fun h => hy2 (Fin.ext h)
  -- y is not row 3 or row 4: those are boolean at column 2
  have hyv3 : y.val ≠ 3 := by
    intro h
    have hy_eq : y = ⟨3, by omega⟩ := Fin.ext h
    have h23 : dotN N h5 ⟨3, by omega⟩ ⟨2, by omega⟩ = ⟨0, by omega⟩ :=
      Fin.ext (dotN_row3_no_val h5 ⟨2, by omega⟩
        (show (2 : Nat) ≠ 3 by omega) (show (2 : Nat) ≠ 4 by omega))
    rcases (hyN ⟨2, by omega⟩).resolve_left (fin_ne' _ _ (by omega))
      |>.resolve_left (fin_ne' _ _ (by omega)) with ⟨h1, h2⟩
    rw [hy_eq, h23] at h1
    exact h1 rfl
  have hyv4 : y.val ≠ 4 := by
    intro h
    have hy_eq : y = ⟨4, by omega⟩ := Fin.ext h
    have h24 : dotN N h5 ⟨4, by omega⟩ ⟨2, by omega⟩ = ⟨0, by omega⟩ :=
      Fin.ext (dotN_row4_no_val h5 ⟨2, by omega⟩
        (show (2 : Nat) ≠ 1 by omega) (show (2 : Nat) ≠ 3 by omega)
        (show (2 : Nat) ≠ 4 by omega))
    rcases (hyN ⟨2, by omega⟩).resolve_left (fin_ne' _ _ (by omega))
      |>.resolve_left (fin_ne' _ _ (by omega)) with ⟨h1, h2⟩
    rw [hy_eq, h24] at h1
    exact h1 rfl
  by_cases hy2v : y.val = 2
  · -- y is the identity row
    have hy_eq : y = ⟨2, by omega⟩ := Fin.ext hy2v
    rw [hy_eq, dotN_row2_eq]
    exact ⟨id, id⟩
  · -- y ≥ 5: identity with columns 2 and y swapped
    have hy5 : 5 ≤ y.val := by omega
    by_cases hx2v : x.val = 2
    · -- output is y itself, and x = 2 is a non-classifier
      have hx_eq : x = ⟨2, by omega⟩ := Fin.ext hx2v
      have hout : dotN N h5 y x = y := by
        rw [hx_eq]
        exact Fin.ext (dotN_rowk_col2_val h5 y hy5)
      constructor
      · intro hxC
        exfalso
        rw [hx_eq] at hxC
        rcases (hxC ⟨2, by omega⟩).resolve_left (fin_ne' _ _ (by omega))
          |>.resolve_left (fin_ne' _ _ (by omega)) with h | h
        · rw [dotN_row2_eq] at h
          exact fin_ne' _ _ (by omega) h
        · rw [dotN_row2_eq] at h
          exact fin_ne' _ _ (by omega) h
      · intro _
        rw [hout]
        exact hyN
    · by_cases hxk : x.val = y.val
      · -- output is the element 2, and x = y is a non-classifier
        have hx_eq : x = y := Fin.ext hxk
        have hout : dotN N h5 y x = ⟨2, by omega⟩ := by
          rw [hx_eq]
          exact Fin.ext (dotN_rowk_colk_val h5 y hy5)
        constructor
        · intro hxC
          exfalso
          rw [hx_eq] at hxC
          rcases (hxC ⟨2, by omega⟩).resolve_left (fin_ne' _ _ (by omega))
            |>.resolve_left (fin_ne' _ _ (by omega)) with h | h <;>
            rcases (hyN ⟨2, by omega⟩).resolve_left (fin_ne' _ _ (by omega))
              |>.resolve_left (fin_ne' _ _ (by omega)) with ⟨h1, h2⟩
          · exact h1 h
          · exact h2 h
        · intro _
          rw [hout]
          intro t
          by_cases ht1 : t = (⟨0, by omega⟩ : Fin N)
          · exact Or.inl ht1
          by_cases ht2 : t = (⟨1, by omega⟩ : Fin N)
          · exact Or.inr (Or.inl ht2)
          · rw [dotN_row2_eq]
            exact Or.inr (Or.inr ⟨ht1, ht2⟩)
      · -- generic column: output is x itself
        have hout : dotN N h5 y x = x :=
          Fin.ext (dotN_rowk_other_val h5 y x hy5 hx2v hxk)
        rw [hout]
        exact ⟨id, id⟩

/-- **The class-preserving sorted world exists at every N ≥ 5**: the
    canonical scaling family is sorted. Together with `swap_balance`,
    the two S-compatible sorted worlds are fully separated by size:
    class-preserving at every N ≥ 5, class-swapping only at even core
    sizes (minimum N = 6, `swap6`). -/
theorem witnessAllN_sorted (N : Nat) (h5 : 5 ≤ N) :
    Sorted N (dotN N h5) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  apply sorted_of_preserving N (dotN N h5) ⟨0, by omega⟩ ⟨1, by omega⟩
    ?_ ⟨3, by omega⟩ (fin_ne' _ _ (by omega)) (fin_ne' _ _ (by omega))
    (fun t => Or.inr (Or.inr (cls_boolean_dotN h5 t)))
    (witnessAllN_class_preserving N h5)
  intro y
  by_cases hy1 : y = (⟨0, by omega⟩ : Fin N)
  · exact Or.inl hy1
  by_cases hy2 : y = (⟨1, by omega⟩ : Fin N)
  · exact Or.inr (Or.inl hy2)
  rcases dichotomy_dotN h5 y hy1 hy2 with h | h
  · refine Or.inr (Or.inr (Or.inl fun t => ?_))
    by_cases ht1 : t = (⟨0, by omega⟩ : Fin N)
    · exact Or.inl ht1
    by_cases ht2 : t = (⟨1, by omega⟩ : Fin N)
    · exact Or.inr (Or.inl ht2)
    · exact Or.inr (Or.inr (h t ht1 ht2))
  · refine Or.inr (Or.inr (Or.inr fun t => ?_))
    by_cases ht1 : t = (⟨0, by omega⟩ : Fin N)
    · exact Or.inl ht1
    by_cases ht2 : t = (⟨1, by omega⟩ : Fin N)
    · exact Or.inr (Or.inl ht2)
    · exact Or.inr (Or.inr (h t ht1 ht2))

end Dichotomic

import Magma.Dichotomic
import Magma.E2PM

/-!
# One-Sided vs Mutual-Inverse Retraction: A Separating Witness

The paper's retraction-pair convention (Section 2, "Retraction pair
convention") distinguishes two conditions on a pair `(s, r)`:

  * **One-sided** (the paper's FRM definition): `∀ x ∈ core, r · (s · x) = x`
  * **Mutual-inverse** (adopted throughout, matching `HasRetractPair`):
    additionally `∀ x ∈ core, s · (r · x) = x`

The paper claims the distinction is "load-bearing, not stylistic" and that
the `|S| ≥ 5` bound under mutual-inverse with `s ≠ r` (Theorem
"Cardinality Bounds") cannot be weakened to the one-sided hypothesis.
Both claims are non-vacuous only if a one-sided-only pair with `s ≠ r`
exists at some `N < 5`.

This file exhibits such a witness at `N = 4`:

```
    0  1  2  3
0:  0  0  0  0     z₁
1:  1  1  1  1     z₂
2:  1  0  1  3     core (s)
3:  0  2  1  3     core (r)
```

With `s = 2`, `r = 3`:
  * One-sided holds: `3·(2·2) = 3·1 = 2`, `3·(2·3) = 3·3 = 3`.
  * Mutual fails: `2·(3·2) = 2·1 = 0 ≠ 2`.
  * `s ≠ r` and `N = 4`.

Moreover, no `s ≠ r` pair in the full `Fin 4` satisfies mutual-inverse on
this magma (brute-force `decide`). This separates:
  1. Mutual-inverse from one-sided (the extra axiom is non-vacuous).
  2. The `|S| ≥ 5` mutual bound from the corresponding one-sided statement
     (one-sided with `s ≠ r` at `N = 4` is realizable).
-/

set_option autoImplicit false

namespace Dichotomic

section OneSidedSeparation

private def rawOSS : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 3
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 3
  | _, _ => 0

private theorem rawOSS_bound (a b : Fin 4) : rawOSS a.val b.val < 4 := by
  revert a b; decide

/-- The binary operation on the N = 4 separating magma. -/
def dotOSS (a b : Fin 4) : Fin 4 := ⟨rawOSS a.val b.val, rawOSS_bound a b⟩

/-- The N = 4 separating magma is an extensional 2-pointed magma. -/
def ossE2PM : Ext2PointedMagma 4 where
  dot := dotOSS
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

/-- **One-sided retraction is satisfiable with `s ≠ r` at `N = 4`.**

    The pair `(s = 2, r = 3)` in `ossE2PM` is one-sided (`r · (s · x) = x`
    on core) and anchored (`r · z₁ = z₁`), with `s ≠ r` and `s, r ∈ core`. -/
theorem ossE2PM_has_one_sided_s_ne_r :
    ∃ s r : Fin 4,
      s ≠ r ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ 0 ∧ r ≠ 1 ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS r (dotOSS s x) = x) ∧
      dotOSS r 0 = 0 := by
  refine ⟨2, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Mutual-inverse with `s ≠ r` is unsatisfiable on `ossE2PM`.**

    No pair `(s, r)` in `Fin 4` with `s ≠ r` satisfies the full
    mutual-inverse retraction axioms (both `r · (s · x) = x` and
    `s · (r · x) = x` on core, plus anchoring `r · z₁ = z₁`). -/
theorem ossE2PM_no_mutual_s_ne_r :
    ¬ ∃ s r : Fin 4,
      s ≠ r ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS r (dotOSS s x) = x) ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS s (dotOSS r x) = x) ∧
      dotOSS r 0 = 0 := by
  decide

/-- **Separation**: mutual-inverse is strictly stronger than one-sided, and
    the `|S| ≥ 5` bound under mutual-with-`s ≠ r` does not hold under the
    one-sided hypothesis. `ossE2PM` admits a one-sided pair with `s ≠ r` at
    `N = 4`, but no mutual-inverse pair with `s ≠ r`. -/
theorem mutual_strictly_stronger_than_one_sided :
    (∃ s r : Fin 4,
      s ≠ r ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ 0 ∧ r ≠ 1 ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS r (dotOSS s x) = x) ∧
      dotOSS r 0 = 0) ∧
    (¬ ∃ s r : Fin 4,
      s ≠ r ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS r (dotOSS s x) = x) ∧
      (∀ x : Fin 4, x ≠ 0 → x ≠ 1 → dotOSS s (dotOSS r x) = x) ∧
      dotOSS r 0 = 0) :=
  ⟨ossE2PM_has_one_sided_s_ne_r, ossE2PM_no_mutual_s_ne_r⟩

end OneSidedSeparation

end Dichotomic

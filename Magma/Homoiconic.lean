import Magma.Dichotomic
import Magma.ICP
import Magma.E2PM
import Magma.Sorting

/-!
# Homoiconic Introspection: the Quotation Law is Determined by the World

Continuing the connecting-axiom program: after sorting, the next axiom
is **sort-introspection** — an internal classifier κ that decides the
C/N partition itself (`data?`/`judge?` in Lisp terms). SAT search over
sorted S+D+C magmas (swap and preserving worlds, N = 6..16) shows the
introspection axiom *determines the quotation law of κ*, and this file
proves it:

- `introspection_negates_of_swapping`: in the swap world, κ ⬝ (s ⬝ x)
  always **differs** from κ ⬝ x — "x is a judge iff (quote x) is data."
  Corollary: quote-transparency of an introspective classifier is
  impossible in the swap world (`no_transparent_introspection_of_swapping`;
  SAT-confirmed UNSAT at N = 6, 8, 10, 16).

- `introspection_transparent_of_preserving`: in the preserving world,
  κ ⬝ (s ⬝ x) always **equals** κ ⬝ x. Corollary: quote-negation of an
  introspective classifier is impossible in the preserving world
  (`no_negating_introspection_of_preserving`).

So a homoiconic system does not choose its introspection law: the typed
world forces transparency, the quoting world forces negation.

## The canonical homoiconic kernel (N = 6)

The minimal magma satisfying everything at once — S, D, C, sorted swap
world, introspection, negation, judge-closure — found by SAT and frozen
below. Its six elements read as a complete Lisp kernel:

```
     0  1  2  3  4  5
  0 [0, 0, 0, 0, 0, 0]   ← halt-true  (absorber)
  1 [1, 1, 1, 1, 1, 1]   ← halt-false (absorber)
  2 [1, 0, 5, 4, 2, 3]   ← QUOTE (s): 4-cycle (2 5 3 4) on core
  3 [0, 0, 4, 5, 3, 2]   ← EVAL  (r): the inverse 4-cycle
  4 [0, 0, 1, 1, 0, 0]   ← data?  (κ): the sort predicate
  5 [0, 0, 0, 0, 1, 1]   ← judge?     : its complement
```

The single internal composition is the homoiconicity law itself:
`judge? = data? ∘ quote` (ICP triple (5, 2, 4)). Quotation has order 4
— `quote²` is a non-trivial involution and `quote⁴ = id` on core — so
the kernel contains a genuine square root of the quote/eval round trip.
-/

set_option autoImplicit false

namespace Dichotomic

/-- **Sort-introspection**: κ internally decides the C/N partition,
    answering z₁ on classifiers and z₂ on non-classifiers. -/
@[reducible] def SortIntrospection (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) (κ : Fin n) : Prop :=
  ∀ y : Fin n, y ≠ z₁ → y ≠ z₂ →
    (ClsSide n dot z₁ z₂ y → dot κ y = z₁) ∧
    (NclSide n dot z₁ z₂ y → dot κ y = z₂)

instance (n : Nat) (dot : Fin n → Fin n → Fin n) (z₁ z₂ κ : Fin n) :
    Decidable (SortIntrospection n dot z₁ z₂ κ) :=
  Fintype.decidableForallFintype

-- ═══════════════════════════════════════════════════════════════════
-- The determination theorems
-- ═══════════════════════════════════════════════════════════════════

/-- **In the swap world, introspection negates under quotation**:
    κ ⬝ (s ⬝ x) ≠ κ ⬝ x for every core x. "x is a judge iff (quote x)
    is data." -/
theorem introspection_negates_of_swapping (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) (hz : z₁ ≠ z₂)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (hswap : ClassSwapping n dot z₁ z₂)
    (s : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hsN : NclSide n dot z₁ z₂ s)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ) :
    ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) ≠ dot κ x := by
  intro x hx1 hx2
  have hout : dot s x ≠ z₁ ∧ dot s x ≠ z₂ :=
    ((hsN x).resolve_left hx1).resolve_left hx2
  rcases hdich x with h | h | h | h
  · exact absurd h hx1
  · exact absurd h hx2
  · -- x is a judge, so quote x is data: κ answers z₁ then z₂
    have h1 : dot κ x = z₁ := (hκ x hx1 hx2).1 h
    have h2 : dot κ (dot s x) = z₂ :=
      (hκ _ hout.1 hout.2).2 ((hswap s x hs1 hs2 hx1 hx2 hsN).1 h)
    rw [h1, h2]
    exact fun hh => hz hh.symm
  · -- x is data, so quote x is a judge: κ answers z₂ then z₁
    have h1 : dot κ x = z₂ := (hκ x hx1 hx2).2 h
    have h2 : dot κ (dot s x) = z₁ :=
      (hκ _ hout.1 hout.2).1 ((hswap s x hs1 hs2 hx1 hx2 hsN).2 h)
    rw [h1, h2]
    exact hz

/-- Corollary: a quote-transparent introspective classifier is impossible
    in the swap world (SAT-confirmed UNSAT at N = 6, 8, 10, 16). -/
theorem no_transparent_introspection_of_swapping (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) (hz : z₁ ≠ z₂)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (hswap : ClassSwapping n dot z₁ z₂)
    (s : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hsN : NclSide n dot z₁ z₂ s)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ) :
    ¬ ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) = dot κ x := by
  intro htrans
  exact introspection_negates_of_swapping n dot z₁ z₂ hz hdich hswap
    s hs1 hs2 hsN κ hκ s hs1 hs2 (htrans s hs1 hs2)

/-- **In the preserving world, introspection is quote-transparent**:
    κ ⬝ (s ⬝ x) = κ ⬝ x for every core x. -/
theorem introspection_transparent_of_preserving (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (hpres : ClassPreserving n dot z₁ z₂)
    (s : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hsN : NclSide n dot z₁ z₂ s)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ) :
    ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) = dot κ x := by
  intro x hx1 hx2
  have hout : dot s x ≠ z₁ ∧ dot s x ≠ z₂ :=
    ((hsN x).resolve_left hx1).resolve_left hx2
  rcases hdich x with h | h | h | h
  · exact absurd h hx1
  · exact absurd h hx2
  · rw [(hκ x hx1 hx2).1 h,
      (hκ _ hout.1 hout.2).1 ((hpres s x hs1 hs2 hx1 hx2 hsN).1 h)]
  · rw [(hκ x hx1 hx2).2 h,
      (hκ _ hout.1 hout.2).2 ((hpres s x hs1 hs2 hx1 hx2 hsN).2 h)]

/-- Corollary: a quote-negating introspective classifier is impossible
    in the preserving world (SAT-confirmed UNSAT at N = 6, 8, 10). -/
theorem no_negating_introspection_of_preserving (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (hpres : ClassPreserving n dot z₁ z₂)
    (s : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hsN : NclSide n dot z₁ z₂ s)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ) :
    ¬ ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) ≠ dot κ x := by
  intro hneg
  exact hneg s hs1 hs2 (introspection_transparent_of_preserving n dot z₁ z₂
    hdich hpres s hs1 hs2 hsN κ hκ s hs1 hs2)

-- ═══════════════════════════════════════════════════════════════════
-- The canonical homoiconic kernel at N = 6
-- ═══════════════════════════════════════════════════════════════════

private def rawK6 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 5 | 2, 3 => 4 | 2, 4 => 2 | 2, 5 => 3
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 4 | 3, 3 => 5 | 3, 4 => 3 | 3, 5 => 2
  | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 1 | 4, 3 => 1 | 4, 4 => 0 | 4, 5 => 0
  | 5, 0 => 0 | 5, 1 => 0 | 5, 2 => 0 | 5, 3 => 0 | 5, 4 => 1 | 5, 5 => 1
  | _, _ => 0

private theorem rawK6_bound (a b : Fin 6) : rawK6 a.val b.val < 6 := by
  revert a b; decide

def dotK6 (a b : Fin 6) : Fin 6 := ⟨rawK6 a.val b.val, rawK6_bound a b⟩

/-- The kernel is a full FaithfulRetractMagma with quote = 2, eval = 3. -/
def kernel6_frm : FaithfulRetractMagma 6 where
  dot := dotK6
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

theorem kernel6_has_retract : HasRetractPair 6 dotK6 0 1 := by decide
theorem kernel6_has_dichotomy : HasDichotomy 6 dotK6 0 1 := by decide
theorem kernel6_has_icp : HasICP 6 dotK6 0 1 := by decide
theorem kernel6_sorted : Sorted 6 dotK6 0 1 := by decide
theorem kernel6_swapping : ClassSwapping 6 dotK6 0 1 := by decide

/-- κ = 4 (`data?`) internally decides the sort partition. -/
theorem kernel6_introspection : SortIntrospection 6 dotK6 0 1 4 := by decide

/-- The introspection law: `data?` negates under quotation, as forced by
    `introspection_negates_of_swapping`. -/
theorem kernel6_negation :
    ∀ x : Fin 6, x ≠ 0 → x ≠ 1 → dotK6 4 (dotK6 2 x) ≠ dotK6 4 x := by decide

/-- **The homoiconicity law is the kernel's internal composition**:
    `judge? = data? ∘ quote` — the ICP triple (5, 2, 4). -/
theorem kernel6_icp_through_quote :
    ∀ x : Fin 6, x ≠ 0 → x ≠ 1 → dotK6 5 x = dotK6 4 (dotK6 2 x) := by decide

/-- Quotation has order 4 on the core: `quote²` is a non-trivial
    involution ("half of eval"), `quote⁴ = id`. -/
theorem kernel6_quote_order_four :
    (∀ x : Fin 6, x ≠ 0 → x ≠ 1 →
      dotK6 2 (dotK6 2 (dotK6 2 (dotK6 2 x))) = x) ∧
    ¬ (∀ x : Fin 6, x ≠ 0 → x ≠ 1 → dotK6 2 (dotK6 2 x) = x) := by decide

/-- **The canonical homoiconic kernel**: six elements — two halt states,
    quote, eval, `data?`, `judge?` — carrying S, D, C, the sorted swap
    world, sort-introspection, and the forced negation law, with the
    single internal composition being homoiconicity itself. -/
theorem canonical_kernel :
    ∃ (_ : FaithfulRetractMagma 6),
      HasRetractPair 6 dotK6 0 1 ∧ HasDichotomy 6 dotK6 0 1 ∧
      HasICP 6 dotK6 0 1 ∧ Sorted 6 dotK6 0 1 ∧
      ClassSwapping 6 dotK6 0 1 ∧ SortIntrospection 6 dotK6 0 1 4 :=
  ⟨kernel6_frm, kernel6_has_retract, kernel6_has_dichotomy,
    kernel6_has_icp, kernel6_sorted, kernel6_swapping, kernel6_introspection⟩

end Dichotomic

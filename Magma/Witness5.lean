import Magma.Dichotomic
import Magma.ICP

/-!
# Canonical N=5 S+D+C Coexistence Witness (indicator magma)

A concrete 5-element S+D+C magma chosen by structural principle rather
than engineering convenience. The two principles:

  1. **Indicator-style classifiers.** Reading absorbers as Boolean
     truth values (z₁ = FALSE, z₂ = TRUE — which is what D *is*
     topos-theoretically, with Ω = 1+1), each classifier τᵢ is the
     characteristic function of {τᵢ, z₂}: τᵢ(x) = z₂ iff x ∈ {τᵢ, z₂},
     else z₁. So τᵢ identifies itself as TRUE and preserves both
     truth labels.

  2. **Non-classifier as classifier-swap.** The unique non-classifier g
     acts on core as the transposition (τ₁ τ₂), with g·g = g and g
     fixing both absorbers. So the magma's classifier-swap symmetry
     (which the mirror-row theorem identifies as the only possible
     non-trivial automorphism at N=5) is *internalised* — it lives
     inside the magma as g's action on core.

```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ = FALSE (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ = TRUE  (absorber)
  2 [0, 1, 1, 0, 0]   ← τ₁: indicator of {τ₁, z₂}
  3 [0, 1, 0, 1, 0]   ← τ₂: indicator of {τ₂, z₂}
  4 [0, 1, 3, 2, 4]   ← g = sec = ret: swaps τ₁↔τ₂ on core, fixes Z and self
```

Category distribution:
  Zeros (2):           {0, 1}
  Classifiers (2):     {2, 3}
  Non-classifiers (1): {4}

ICP triple: `(a, b, c) = (2, 4, 3)`. With b = g acting as the swap,
the factorisation a·x = c·(b·x) on core is non-trivial — it's the
classifier-swap rewriting itself.

This witness is non-rigid: |Aut| = 2, with the unique non-trivial
automorphism being the transposition (τ₁ τ₂) — which is exactly g's
own action on core. Mirror-row (Theorem 4.13) then ensures this is the
*only* possible non-trivial automorphism at N=5.

**Optimal minimum cardinality**: N=5 is the smallest possible witness
for R+D+H coexistence (`no_icp_at_4` below). The simpler "identity on
core" alternative — what the paper used to use as `dotW5` — is rigid
but doesn't internalise its symmetry; this canonical witness sacrifices
rigidity for structural transparency.
-/

set_option autoImplicit false

namespace Dichotomic

-- ═══════════════════════════════════════════════════════════════════
-- The N=5 R+D+ICP witness
-- ═══════════════════════════════════════════════════════════════════

private def rawW5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 1 | 2, 3 => 0 | 2, 4 => 0
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 3 | 4, 3 => 2 | 4, 4 => 4
  | _, _ => 0

private theorem rawW5_bound (a b : Fin 5) : rawW5 a.val b.val < 5 := by
  revert a b; decide

def dotW5 (a b : Fin 5) : Fin 5 := ⟨rawW5 a.val b.val, rawW5_bound a b⟩

-- ═══════════════════════════════════════════════════════════════════
-- Capability R: FaithfulRetractMagma (self-representation)
-- ═══════════════════════════════════════════════════════════════════

/-- The canonical N=5 witness is a FaithfulRetractMagma with sec = ret = 4
    (the unique non-classifier g, acting on core as the classifier swap and
    fixing absorbers). -/
def witness5_frm : FaithfulRetractMagma 5 where
  dot := dotW5
  zero₁ := 0
  zero₂ := 1
  sec := 4
  ret := 4
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Capability D: DichotomicRetractMagma (self-description)
-- ═══════════════════════════════════════════════════════════════════

/-- The canonical N=5 witness is a DichotomicRetractMagma with τ=2 (one of
    the two indicator classifiers; the other, τ=3, would do equally — they
    are exchanged by the magma's classifier-swap automorphism). -/
def witness5_drm : DichotomicRetractMagma 5 where
  dot := dotW5
  zero₁ := 0
  zero₂ := 1
  sec := 4
  ret := 4
  cls := 2
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide
  cls_boolean := by decide
  cls_ne_zero₁ := by decide
  cls_ne_zero₂ := by decide
  dichotomy := by decide
  has_non_classifier := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Capability H: ICP (self-execution)
-- ═══════════════════════════════════════════════════════════════════

/-- ICP holds at N=5, witnessed by a=2, b=4, c=3. With b=g acting as the
    classifier swap on core, the factorisation `a·x = c·(b·x)` is the
    classifier-swap identity τ₁(x) = τ₂(g(x)) — the two indicator
    classifiers exchange under the swap they internalise. -/
theorem w5_has_icp : HasICP 5 dotW5 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Coexistence witness theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **Lean-verified coexistence**: R+D+ICP all hold at N=5.
    This is the smallest possible witness for simultaneous R+D+H
    (at N=4, ICP is vacuously false since only 2 core elements exist). -/
theorem sdh_witness_5 :
    ∃ (_ : FaithfulRetractMagma 5),
    ∃ (_ : DichotomicRetractMagma 5),
    HasICP 5 dotW5 0 1 :=
  ⟨witness5_frm, witness5_drm, w5_has_icp⟩

-- ═══════════════════════════════════════════════════════════════════
-- Optimality: N=4 is impossible
-- ═══════════════════════════════════════════════════════════════════

/-- **N=5 is optimal**: At N=4, ICP fails for any E2PM (only 2 core elements,
    but ICP needs 3 pairwise distinct non-absorbers). Combined with
    `sdh_witness_5`, this shows N=5 is the minimum cardinality for
    R+D+H coexistence.

    Proof: ICP requires a, b, c pairwise distinct, all ∉ {0,1}. In Fin 4,
    the only non-absorbers are {2, 3} — a 2-element set cannot contain
    3 distinct elements. Pure pigeonhole, no `decide`. -/
theorem no_icp_at_4 (dot : Fin 4 → Fin 4 → Fin 4) : ¬ HasICP 4 dot 0 1 := by
  intro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, _, _, _⟩
  have mem : ∀ (x : Fin 4), x ≠ 0 → x ≠ 1 → x = 2 ∨ x = 3 := by decide
  rcases mem a ha1 ha2 with rfl | rfl <;> rcases mem b hb1 hb2 with rfl | rfl <;>
    rcases mem c hc1 hc2 with rfl | rfl <;> simp_all

end Dichotomic

import Magma.Dichotomic
import Magma.ICP

/-!
# Structural D without the non-classifier-existence axiom

`DichotomicRetractMagma` (in `Magma.Dichotomic`) bundles three D-side
ingredients:
  (a) a full classifier `cls` whose row lies in {zero₁, zero₂},
  (b) the dichotomy on core,
  (c) `has_non_classifier`: the non-classifier class is inhabited.

This file isolates the structural fragment `D_struct = (a) ∧ (b)` and shows
that clause (c) is *redundant* once `HasICP` is also assumed: the middle
element `b` of any ICP triple is core-preserving, hence a non-classifier,
and the ICP non-triviality clause supplies the required core element `x`.

The main artefacts:

  * `DStructRetractMagma n` — D's structural fragment on top of an FRM.
  * `DStructRetractMagma.has_non_classifier_of_icp` — the upgrade lemma.
  * `DichotomicRetractMagma.ofDStructICP` — explicit construction recovering
    a full `DichotomicRetractMagma` from `D_struct + HasICP`.

Combined with `HasICP`, this matches the joint-S+D+C definition with one
fewer field than `DichotomicRetractMagma + HasICP` would otherwise carry.
-/

set_option autoImplicit false

namespace Dichotomic

-- ══════════════════════════════════════════════════════════════════════
-- D minus has_non_classifier
-- ══════════════════════════════════════════════════════════════════════

/-- `D_struct` on top of a `FaithfulRetractMagma`: the structural fragment
    of the classifier dichotomy.

    Compared to `DichotomicRetractMagma`, the `has_non_classifier`
    existential is omitted. When ICP is also assumed, that existential is
    a *consequence*, not a hypothesis (see
    `DStructRetractMagma.has_non_classifier_of_icp`). -/
structure DStructRetractMagma (n : Nat) extends FaithfulRetractMagma n where
  /-- A classifier: a non-constant transformation whose row is entirely
      in {zero₁, zero₂}. -/
  cls : Fin n
  /-- The classifier maps all inputs into {zero₁, zero₂}. -/
  cls_boolean : ∀ x : Fin n, dot cls x = zero₁ ∨ dot cls x = zero₂
  /-- The classifier is not zero₁ (non-degeneracy). -/
  cls_ne_zero₁ : cls ≠ zero₁
  /-- The classifier is not zero₂ (non-degeneracy). -/
  cls_ne_zero₂ : cls ≠ zero₂
  /-- Every non-absorber is either all-{0,1} or all-out on core. -/
  dichotomy : ∀ y : Fin n, y ≠ zero₁ → y ≠ zero₂ →
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x = zero₁ ∨ dot y x = zero₂) ∨
    (∀ x : Fin n, x ≠ zero₁ → x ≠ zero₂ →
      dot y x ≠ zero₁ ∧ dot y x ≠ zero₂)

-- ══════════════════════════════════════════════════════════════════════
-- The upgrade lemma: ICP supplies the missing axiom
-- ══════════════════════════════════════════════════════════════════════

/-- **`has_non_classifier` is derivable from `D_struct + HasICP`.**

    The middle element `b` of any ICP triple is core-preserving by clause (1)
    of `HasICP`, hence a non-classifier. The non-triviality clause (3)
    supplies a core element `x` to use as the witness, since `x ≠ zero₁`
    and `x ≠ zero₂` and core-preservation of `b` then gives
    `dot b x ≠ zero₁ ∧ dot b x ≠ zero₂`. -/
theorem DStructRetractMagma.has_non_classifier_of_icp
    {n : Nat} (M : DStructRetractMagma n)
    (hICP : HasICP n M.dot M.zero₁ M.zero₂) :
    ∃ y : Fin n, y ≠ M.zero₁ ∧ y ≠ M.zero₂ ∧
      ∃ x : Fin n, x ≠ M.zero₁ ∧ x ≠ M.zero₂ ∧
        M.dot y x ≠ M.zero₁ ∧ M.dot y x ≠ M.zero₂ := by
  obtain ⟨_a, b, _c, _hab, _hac, _hbc, _ha1, _ha2, hb1, hb2, _hc1, _hc2,
          hpres, _hfact, ⟨x, _y, hx1, hx2, _hy1, _hy2, _hneq⟩⟩ := hICP
  refine ⟨b, hb1, hb2, x, hx1, hx2, ?_, ?_⟩
  · have h := hpres x
    rcases h with h | h | ⟨h1, _⟩
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h1
  · have h := hpres x
    rcases h with h | h | ⟨_, h2⟩
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h2

-- ══════════════════════════════════════════════════════════════════════
-- Bridge: from D_struct + HasICP recover a DichotomicRetractMagma
-- ══════════════════════════════════════════════════════════════════════

/-- **Joint upgrade**: a `DStructRetractMagma` together with an ICP proof
    is a full `DichotomicRetractMagma`. The `has_non_classifier` field is
    supplied by `has_non_classifier_of_icp`.

    Demonstrates the axiom reduction: the canonical S+D+C bundle can be
    built from one fewer hypothesis than `DichotomicRetractMagma + HasICP`
    states, since `has_non_classifier` is recovered as a theorem. -/
def DichotomicRetractMagma.ofDStructICP {n : Nat}
    (M : DStructRetractMagma n)
    (hICP : HasICP n M.dot M.zero₁ M.zero₂) :
    DichotomicRetractMagma n where
  toFaithfulRetractMagma := M.toFaithfulRetractMagma
  cls := M.cls
  cls_boolean := M.cls_boolean
  cls_ne_zero₁ := M.cls_ne_zero₁
  cls_ne_zero₂ := M.cls_ne_zero₂
  dichotomy := M.dichotomy
  has_non_classifier := M.has_non_classifier_of_icp hICP

-- ══════════════════════════════════════════════════════════════════════
-- Forgetful direction (sanity check)
-- ══════════════════════════════════════════════════════════════════════

/-- A full `DichotomicRetractMagma` forgets its `has_non_classifier` field
    to yield a `DStructRetractMagma`. -/
def DichotomicRetractMagma.toDStruct {n : Nat}
    (M : DichotomicRetractMagma n) : DStructRetractMagma n where
  toFaithfulRetractMagma := M.toFaithfulRetractMagma
  cls := M.cls
  cls_boolean := M.cls_boolean
  cls_ne_zero₁ := M.cls_ne_zero₁
  cls_ne_zero₂ := M.cls_ne_zero₂
  dichotomy := M.dichotomy

end Dichotomic

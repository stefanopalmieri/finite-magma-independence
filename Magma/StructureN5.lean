import Magma.CatKripkeWallMinimal
import Magma.ICP
import Mathlib.Data.Finset.Card

/-!
# N=5 Structure Theorem

This file formalises the content of the paper's Theorem 4.8 (Structure Theorem
at N=5) and Corollary 4.10 (strong S is absent at N=5):

> Let `M` be a DichotomicRetractMagma on `Fin 5` satisfying ICP.
> Then the core of `M` contains exactly one non-classifier; in particular
> `M.sec = M.ret`.

The proof proceeds by combining two universal-N lemmas with the existing
`sec_is_non_classifier` and `ret_is_non_classifier` results:

  * `h_triple_coherence` — the outer elements of an ICP witness are either
    both classifiers or both non-classifiers.
  * `unique_non_classifier_at_N5` — at N=5, under the dichotomy plus ICP,
    the non-classifier in core is unique.

Together with the already-proved fact that both `M.sec` and `M.ret` are
non-classifiers, `unique_non_classifier_at_N5` closes Corollary 4.10 in Lean.
This resolves the "machine-checked Lean proof of Theorem 4.8" half of
Open Problem 4 for the key retraction-collapse content of that theorem.
-/

set_option autoImplicit false

namespace KripkeWall

-- ══════════════════════════════════════════════════════════════════════
-- Part 1: H-triple type-coherence (universal N)
-- ══════════════════════════════════════════════════════════════════════

section UniversalN
variable {n : Nat} (M : DichotomicRetractMagma n)

/-- **H-Triple Type-Coherence (paper Theorem 3.12).**

In any dichotomic retract magma `M`, the outer elements `a`, `c` of an ICP
witness `(a, b, c)` are either both classifiers or both non-classifiers.

Input: the raw components of `HasICP` (non-zero, `b` core-preserving,
factorisation `a·x = c·(b·x)` on core). -/
theorem h_triple_coherence
    {a b c : Fin n}
    (ha1 : a ≠ M.zero₁) (ha2 : a ≠ M.zero₂)
    (_hb1 : b ≠ M.zero₁) (_hb2 : b ≠ M.zero₂)
    (hc1 : c ≠ M.zero₁) (hc2 : c ≠ M.zero₂)
    (h_pres : ∀ x : Fin n, x = M.zero₁ ∨ x = M.zero₂ ∨
              (M.dot b x ≠ M.zero₁ ∧ M.dot b x ≠ M.zero₂))
    (h_fact : ∀ x : Fin n, x = M.zero₁ ∨ x = M.zero₂ ∨
              M.dot a x = M.dot c (M.dot b x)) :
    (IsClassifier M a ∧ IsClassifier M c) ∨
    (IsNonClassifier M a ∧ IsNonClassifier M c) := by
  -- Unpack `h_pres` and `h_fact` as conditional implications on core.
  have hpres_core : ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ →
        M.dot b x ≠ M.zero₁ ∧ M.dot b x ≠ M.zero₂ := by
    intro x hx1 hx2
    rcases h_pres x with h | h | h
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h
  have hfact_core : ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ →
        M.dot a x = M.dot c (M.dot b x) := by
    intro x hx1 hx2
    rcases h_fact x with h | h | h
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h
  -- Case-split on the type of `c` via the Kripke dichotomy.
  rcases M.dichotomy c hc1 hc2 with hc_cls | hc_nc
  · -- c is a classifier ⇒ a is a classifier.
    left
    refine ⟨⟨ha1, ha2, ?_⟩, ⟨hc1, hc2, hc_cls⟩⟩
    intro x hx1 hx2
    have hbx_core := hpres_core x hx1 hx2
    have hfact_x := hfact_core x hx1 hx2
    have hc_bx := hc_cls (M.dot b x) hbx_core.1 hbx_core.2
    rw [hfact_x]; exact hc_bx
  · -- c is a non-classifier ⇒ a is a non-classifier.
    right
    refine ⟨⟨ha1, ha2, ?_⟩, ⟨hc1, hc2, hc_nc⟩⟩
    intro x hx1 hx2
    have hbx_core := hpres_core x hx1 hx2
    have hfact_x := hfact_core x hx1 hx2
    have hc_bx := hc_nc (M.dot b x) hbx_core.1 hbx_core.2
    rw [hfact_x]; exact hc_bx

end UniversalN

-- ══════════════════════════════════════════════════════════════════════
-- Part 2: Uniqueness of the non-classifier at N=5
-- ══════════════════════════════════════════════════════════════════════

section SizeFive
variable (M : DichotomicRetractMagma 5)

/-- Technical lemma: `{z₁, z₂, cls, x, y}` is all of `Fin 5` whenever these
    five elements are pairwise distinct. -/
private theorem fin5_five_distinct_covers_univ
    (z₁ z₂ cls x y : Fin 5)
    (h12 : z₁ ≠ z₂)
    (h1c : z₁ ≠ cls) (h1x : z₁ ≠ x) (h1y : z₁ ≠ y)
    (h2c : z₂ ≠ cls) (h2x : z₂ ≠ x) (h2y : z₂ ≠ y)
    (hcx : cls ≠ x) (hcy : cls ≠ y) (hxy : x ≠ y) :
    ({z₁, z₂, cls, x, y} : Finset (Fin 5)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  -- Goal: card = Fintype.card (Fin 5) = 5.
  have h1 : z₁ ∉ ({z₂, cls, x, y} : Finset (Fin 5)) := by
    simp [h12, h1c, h1x, h1y]
  have h2 : z₂ ∉ ({cls, x, y} : Finset (Fin 5)) := by
    simp [h2c, h2x, h2y]
  have h3 : cls ∉ ({x, y} : Finset (Fin 5)) := by
    simp [hcx, hcy]
  have h4 : x ∉ ({y} : Finset (Fin 5)) := by
    simp [hxy]
  rw [show ({z₁, z₂, cls, x, y} : Finset (Fin 5)) =
          insert z₁ (insert z₂ (insert cls (insert x {y}))) from rfl,
      Finset.card_insert_of_notMem h1,
      Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3,
      Finset.card_insert_of_notMem h4,
      Finset.card_singleton, Fintype.card_fin]

/-- At N=5 under the Kripke dichotomy plus ICP, the non-classifier in core
    is unique. -/
theorem unique_non_classifier_at_N5
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂)
    {x y : Fin 5}
    (hx_nc : IsNonClassifier M x)
    (hy_nc : IsNonClassifier M y) :
    x = y := by
  by_contra hxy
  -- Extract field data.
  obtain ⟨hx1, hx2, hx_row⟩ := hx_nc
  obtain ⟨hy1, hy2, hy_row⟩ := hy_nc
  -- M.cls is a classifier distinct from x, y, z₁, z₂.
  have hcls1 := M.cls_ne_zero₁
  have hcls2 := M.cls_ne_zero₂
  -- cls ≠ x: classifiers and non-classifiers disagree on every core element.
  have hclsx : M.cls ≠ x := by
    intro h
    -- cls_boolean says cls·y ∈ {z₁, z₂} for all y; hx_row says x·y ∉ {z₁, z₂} on core.
    -- Apply on any core element, say pick `x` itself since x ≠ z₁, z₂.
    rcases M.cls_boolean x with h0 | h0
    · exact (hx_row x hx1 hx2).1 (h ▸ h0)
    · exact (hx_row x hx1 hx2).2 (h ▸ h0)
  have hclsy : M.cls ≠ y := by
    intro h
    rcases M.cls_boolean y with h0 | h0
    · exact (hy_row y hy1 hy2).1 (h ▸ h0)
    · exact (hy_row y hy1 hy2).2 (h ▸ h0)
  -- Unpack ICP witness.
  obtain ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
          hpres, hfact, _hnont⟩ := hC
  -- By fin5 coverage, each of a, b, c lies in {z₁, z₂, cls, x, y}.
  -- Since a, b, c ≠ z₁, z₂, each lies in {cls, x, y}.
  have hcov : ({M.zero₁, M.zero₂, M.cls, x, y} : Finset (Fin 5)) = Finset.univ := by
    apply fin5_five_distinct_covers_univ
    · exact M.zeros_distinct
    · exact fun h => hcls1 h.symm
    · exact fun h => hx1 h.symm
    · exact fun h => hy1 h.symm
    · exact fun h => hcls2 h.symm
    · exact fun h => hx2 h.symm
    · exact fun h => hy2 h.symm
    · exact hclsx
    · exact hclsy
    · exact hxy
  have mem_univ : ∀ z : Fin 5, z ∈ ({M.zero₁, M.zero₂, M.cls, x, y} : Finset (Fin 5)) := by
    intro z; rw [hcov]; exact Finset.mem_univ z
  -- Each of a, b, c is in {cls, x, y}.
  have classify : ∀ z : Fin 5, z ≠ M.zero₁ → z ≠ M.zero₂ →
        z = M.cls ∨ z = x ∨ z = y := by
    intro z hz1 hz2
    have := mem_univ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h | h
    · exact absurd h hz1
    · exact absurd h hz2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- Apply h_triple_coherence to (a, b, c).
  have hcoh := h_triple_coherence M ha1 ha2 hb1 hb2 hc1 hc2 hpres hfact
  -- Now split on the coherence case.
  rcases hcoh with ⟨ha_cls, hc_cls⟩ | ⟨ha_nc, hc_nc⟩
  · -- a and c are both classifiers. Each equals cls, x, or y.
    -- But x, y are non-classifiers, so neither a nor c can be x or y
    -- (classifier_not_non_classifier). Hence a = cls and c = cls, giving a = c.
    have ha_eq : a = M.cls := by
      rcases classify a ha1 ha2 with hcls | hx | hy
      · exact hcls
      · -- a = x would make a both classifier and non-classifier. Contradiction.
        exfalso
        have : IsNonClassifier M a := ⟨ha1, ha2, hx ▸ hx_row⟩
        exact classifier_not_non_classifier M a ha_cls this
      · exfalso
        have : IsNonClassifier M a := ⟨ha1, ha2, hy ▸ hy_row⟩
        exact classifier_not_non_classifier M a ha_cls this
    have hc_eq : c = M.cls := by
      rcases classify c hc1 hc2 with hcls | hx | hy
      · exact hcls
      · exfalso
        have : IsNonClassifier M c := ⟨hc1, hc2, hx ▸ hx_row⟩
        exact classifier_not_non_classifier M c hc_cls this
      · exfalso
        have : IsNonClassifier M c := ⟨hc1, hc2, hy ▸ hy_row⟩
        exact classifier_not_non_classifier M c hc_cls this
    exact hac (ha_eq.trans hc_eq.symm)
  · -- a and c are both non-classifiers. Each is in {cls, x, y}.
    -- a = cls is impossible (cls is classifier). So a ∈ {x, y}, similarly c.
    -- With a ≠ c, {a, c} = {x, y}. Hence b ∈ {cls} = one remaining element.
    -- But b core-preserving contradicts cls being a classifier.
    have ha_eq : a = x ∨ a = y := by
      rcases classify a ha1 ha2 with hcls | hx | hy
      · exfalso
        -- a = cls would make cls a non-classifier — contradiction with cls_boolean.
        have hcls_is_cls : IsClassifier M M.cls :=
          ⟨hcls1, hcls2, fun z _ _ => M.cls_boolean z⟩
        apply classifier_not_non_classifier M M.cls hcls_is_cls
        exact hcls ▸ ha_nc
      · exact Or.inl hx
      · exact Or.inr hy
    have hc_eq : c = x ∨ c = y := by
      rcases classify c hc1 hc2 with hcls | hx | hy
      · exfalso
        have hcls_is_cls : IsClassifier M M.cls :=
          ⟨hcls1, hcls2, fun z _ _ => M.cls_boolean z⟩
        apply classifier_not_non_classifier M M.cls hcls_is_cls
        exact hcls ▸ hc_nc
      · exact Or.inl hx
      · exact Or.inr hy
    -- Now show b = cls. b ∈ {cls, x, y}, and b ≠ a, b ≠ c.
    have hb_eq_cls : b = M.cls := by
      rcases classify b hb1 hb2 with hcls | hx | hy
      · exact hcls
      · -- b = x. Then since a ≠ b and c ≠ b, a ≠ x and c ≠ x. So a = y, c = y (by ha_eq/hc_eq). But a ≠ c.
        exfalso
        have ha_ne_x : a ≠ x := fun h => hab (h.trans hx.symm)
        have hc_ne_x : c ≠ x := fun h => hbc (hx.trans h.symm)
        have ha_y : a = y := ha_eq.resolve_left ha_ne_x
        have hc_y : c = y := hc_eq.resolve_left hc_ne_x
        exact hac (ha_y.trans hc_y.symm)
      · -- b = y. Similar.
        exfalso
        have ha_ne_y : a ≠ y := fun h => hab (h.trans hy.symm)
        have hc_ne_y : c ≠ y := fun h => hbc (hy.trans h.symm)
        have ha_x : a = x := ha_eq.resolve_right ha_ne_y
        have hc_x : c = x := hc_eq.resolve_right hc_ne_y
        exact hac (ha_x.trans hc_x.symm)
    -- But b is core-preserving: b · x ∉ {z₁, z₂} on core. With b = cls, cls · x ∈ {z₁, z₂}.
    -- Instantiate at core element x.
    have hpres_x := hpres x
    rcases hpres_x with h0 | h0 | h0
    · exact hx1 h0
    · exact hx2 h0
    · -- dot b x ∉ {z₁, z₂}. But b = cls, and cls · x ∈ {z₁, z₂}.
      rcases M.cls_boolean x with hcls_x | hcls_x
      · exact h0.1 (hb_eq_cls ▸ hcls_x)
      · exact h0.2 (hb_eq_cls ▸ hcls_x)

-- ══════════════════════════════════════════════════════════════════════
-- Part 3: Corollary 4.10 — strong S is absent at N=5
-- ══════════════════════════════════════════════════════════════════════

/-- **Corollary 4.10 (paper).** At N=5, no DichotomicRetractMagma with ICP
    admits a retraction pair with `sec ≠ ret`. Equivalently, the section
    and retraction coincide in every such magma. -/
theorem N5_sec_eq_ret (hC : HasICP 5 M.dot M.zero₁ M.zero₂) :
    M.sec = M.ret :=
  unique_non_classifier_at_N5 M hC (sec_is_non_classifier M) (ret_is_non_classifier M)

/-- **Theorem 4.8(i) (paper).** At N=5 under DRM+ICP, there is a unique
    non-classifier in the carrier. Combined with the existence of `M.cls`
    and distinctness of classifiers from non-classifiers, this pins down
    the core partition as two classifiers plus one non-classifier. -/
theorem N5_exists_unique_non_classifier
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂) :
    ∃! x : Fin 5, IsNonClassifier M x :=
  ⟨M.sec, sec_is_non_classifier M,
    fun _y hy => unique_non_classifier_at_N5 M hC hy (sec_is_non_classifier M)⟩

/-- **Theorem 4.8(iii) (paper) — ICP triple middle is the non-classifier.**
    At N=5, the inner element `b` of any ICP witness `(a, b, c)` coincides
    with `M.sec` (= `M.ret`), and the outer elements `a`, `c` are both
    classifiers. -/
theorem N5_icp_triple_structure
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂) :
    ∃ a b c : Fin 5,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsClassifier M a ∧ IsClassifier M c ∧ b = M.sec := by
  have hC_copy := hC
  obtain ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
          hpres, hfact, _hnont⟩ := hC_copy
  refine ⟨a, b, c, hab, hac, hbc, ?_, ?_, ?_⟩
  · -- a is a classifier. By h_triple_coherence, case split.
    rcases h_triple_coherence M ha1 ha2 hb1 hb2 hc1 hc2 hpres hfact with
      ⟨ha_cls, _⟩ | ⟨ha_nc, hc_nc⟩
    · exact ha_cls
    · -- Both a and c non-classifiers. But a ≠ c means two distinct non-classifiers,
      -- contradicting uniqueness.
      exfalso
      have := unique_non_classifier_at_N5 M hC ha_nc hc_nc
      exact hac this
  · rcases h_triple_coherence M ha1 ha2 hb1 hb2 hc1 hc2 hpres hfact with
      ⟨_, hc_cls⟩ | ⟨ha_nc, hc_nc⟩
    · exact hc_cls
    · exfalso
      have := unique_non_classifier_at_N5 M hC ha_nc hc_nc
      exact hac this
  · -- b is a non-classifier and hence b = M.sec by uniqueness.
    -- Show b is a non-classifier: b is core-preserving (hpres) and in core.
    have hb_nc : IsNonClassifier M b := by
      refine ⟨hb1, hb2, ?_⟩
      intro x hx1 hx2
      rcases hpres x with h | h | h
      · exact absurd h hx1
      · exact absurd h hx2
      · exact h
    exact unique_non_classifier_at_N5 M hC hb_nc (sec_is_non_classifier M)

end SizeFive

/-- Restatement of Corollary 4.10 as "strong S is unsatisfiable at N=5":
    no DRM+ICP on `Fin 5` can have `sec ≠ ret`. -/
theorem N5_no_strong_S :
    ¬ ∃ M : DichotomicRetractMagma 5,
        HasICP 5 M.dot M.zero₁ M.zero₂ ∧ M.sec ≠ M.ret := by
  rintro ⟨M, hC, h_ne⟩
  exact h_ne (N5_sec_eq_ret M hC)

end KripkeWall

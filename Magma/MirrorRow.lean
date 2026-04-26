import Magma.Dichotomic
import Magma.Functoriality
import Magma.ICP
import Magma.StructureN5
import Mathlib.Data.Fintype.Perm

/-!
# Mirror-Row Theorem (paper §`MIRROR_ROW_THEOREM.md`)

For any `DichotomicRetractMagma` on `Fin 5` with `HasICP`, every Cayley-table
automorphism `σ : Equiv.Perm (Fin 5)` fixes both absorbers:

  σ M.zero₁ = M.zero₁  ∧  σ M.zero₂ = M.zero₂.

Equivalently, no automorphism swaps the two absorbers; the Klein-four
"absorber swap" cases (ii) and (iv) of `Aut(M) ≤ Sym(Z) × Sym(C) × {id_g}`
are eliminated.

## Proof outline

* `aut_preserves_left_absorber` — σ takes left-zeros to left-zeros, so σ
  permutes `{z₁, z₂}` (using `no_other_zeros`).
* `aut_preserves_classifier` / `aut_preserves_non_classifier` — direct
  port of `DRMIso.preserves_*` to a single-magma automorphism σ.
* `aut_fixes_unique_non_classifier` — at N=5 + ICP, `M.sec` is the unique
  non-classifier (`unique_non_classifier_at_N5`), so σ must fix it.

Main theorem: assume σ swaps absorbers. Case-split on σ's action on the
two classifiers.

* Case A — σ fixes both classifiers `τ₁`, `τ₂`. Pick `τ = τ₁`. Then
  `τ · τ ∈ Z` and σ-fixed (since σ fixes τ). But σ swaps Z. Contradiction.
* Case B — σ swaps the two classifiers. Use the C-triple factorisation
  `τ₁ · x = τ₂ · (g · x)` at `x = g`, and σ-fixedness `g · g = g`, to
  derive `τ₁ · g = τ₂ · g =: v ∈ Z`. Apply σ: `σ(τ₁ · g) = τ₂ · g = v`.
  So σ fixes v ∈ Z. But σ swaps Z. Contradiction.
-/

set_option autoImplicit false

namespace Dichotomic

variable {n : Nat} (M : DichotomicRetractMagma n)

-- ══════════════════════════════════════════════════════════════════════
-- Step 0: Helper lemmas about automorphisms of a single DRM
-- ══════════════════════════════════════════════════════════════════════

/-- An operation-preserving permutation maps left-absorbers to left-absorbers. -/
private theorem aut_preserves_left_absorber
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (M.dot a b) = M.dot (σ a) (σ b))
    (a : Fin n) (ha : ∀ x, M.dot a x = a) :
    ∀ x, M.dot (σ a) x = σ a := by
  intro x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rw [← h_hom, ha]

/-- σ z₁ ∈ {z₁, z₂}. -/
private theorem aut_zero₁_mem
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (M.dot a b) = M.dot (σ a) (σ b)) :
    σ M.zero₁ = M.zero₁ ∨ σ M.zero₁ = M.zero₂ :=
  M.no_other_zeros (σ M.zero₁)
    (aut_preserves_left_absorber M σ h_hom M.zero₁ M.zero₁_left)

/-- σ z₂ ∈ {z₁, z₂}. -/
private theorem aut_zero₂_mem
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (M.dot a b) = M.dot (σ a) (σ b)) :
    σ M.zero₂ = M.zero₁ ∨ σ M.zero₂ = M.zero₂ :=
  M.no_other_zeros (σ M.zero₂)
    (aut_preserves_left_absorber M σ h_hom M.zero₂ M.zero₂_left)

/-- An automorphism preserves the classifier predicate. -/
private theorem aut_preserves_classifier
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (M.dot a b) = M.dot (σ a) (σ b))
    {a : Fin n} (ha : IsClassifier M a) :
    IsClassifier M (σ a) := by
  obtain ⟨ha₁, ha₂, hrow⟩ := ha
  have hz₁_mem := aut_zero₁_mem M σ h_hom
  have hz₂_mem := aut_zero₂_mem M σ h_hom
  -- σ a ≠ z₁
  have hσa_ne_z₁ : σ a ≠ M.zero₁ := by
    intro h
    rcases hz₁_mem with h₁ | h₁
    · exact ha₁ (σ.injective (h.trans h₁.symm))
    · rcases hz₂_mem with h₂ | h₂
      · exact ha₂ (σ.injective (h.trans h₂.symm))
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
  have hσa_ne_z₂ : σ a ≠ M.zero₂ := by
    intro h
    rcases hz₁_mem with h₁ | h₁
    · rcases hz₂_mem with h₂ | h₂
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
      · exact ha₂ (σ.injective (h.trans h₂.symm))
    · exact ha₁ (σ.injective (h.trans h₁.symm))
  refine ⟨hσa_ne_z₁, hσa_ne_z₂, ?_⟩
  intro y hy₁ hy₂
  obtain ⟨x, rfl⟩ := σ.surjective y
  have hx₁ : x ≠ M.zero₁ := by
    intro hx; subst hx
    rcases hz₁_mem with h | h
    · exact hy₁ h
    · exact hy₂ h
  have hx₂ : x ≠ M.zero₂ := by
    intro hx; subst hx
    rcases hz₂_mem with h | h
    · exact hy₁ h
    · exact hy₂ h
  rw [← h_hom]
  rcases hrow x hx₁ hx₂ with h | h
  · rw [h]
    rcases hz₁_mem with h₁ | h₁
    · exact Or.inl h₁
    · exact Or.inr h₁
  · rw [h]
    rcases hz₂_mem with h₂ | h₂
    · exact Or.inl h₂
    · exact Or.inr h₂

/-- An automorphism preserves the non-classifier predicate. -/
private theorem aut_preserves_non_classifier
    (σ : Equiv.Perm (Fin n))
    (h_hom : ∀ a b : Fin n, σ (M.dot a b) = M.dot (σ a) (σ b))
    {a : Fin n} (ha : IsNonClassifier M a) :
    IsNonClassifier M (σ a) := by
  obtain ⟨ha₁, ha₂, hrow⟩ := ha
  have hz₁_mem := aut_zero₁_mem M σ h_hom
  have hz₂_mem := aut_zero₂_mem M σ h_hom
  have hσa_ne_z₁ : σ a ≠ M.zero₁ := by
    intro h
    rcases hz₁_mem with h₁ | h₁
    · exact ha₁ (σ.injective (h.trans h₁.symm))
    · rcases hz₂_mem with h₂ | h₂
      · exact ha₂ (σ.injective (h.trans h₂.symm))
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
  have hσa_ne_z₂ : σ a ≠ M.zero₂ := by
    intro h
    rcases hz₁_mem with h₁ | h₁
    · rcases hz₂_mem with h₂ | h₂
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
      · exact ha₂ (σ.injective (h.trans h₂.symm))
    · exact ha₁ (σ.injective (h.trans h₁.symm))
  refine ⟨hσa_ne_z₁, hσa_ne_z₂, ?_⟩
  intro y hy₁ hy₂
  obtain ⟨x, rfl⟩ := σ.surjective y
  have hx₁ : x ≠ M.zero₁ := by
    intro hx; subst hx
    rcases hz₁_mem with h | h
    · exact hy₁ h
    · exact hy₂ h
  have hx₂ : x ≠ M.zero₂ := by
    intro hx; subst hx
    rcases hz₂_mem with h | h
    · exact hy₁ h
    · exact hy₂ h
  obtain ⟨hv₁, hv₂⟩ := hrow x hx₁ hx₂
  rw [← h_hom]
  refine ⟨?_, ?_⟩
  · intro h
    rcases hz₁_mem with h₁ | h₁
    · exact hv₁ (σ.injective (h.trans h₁.symm))
    · rcases hz₂_mem with h₂ | h₂
      · exact hv₂ (σ.injective (h.trans h₂.symm))
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
  · intro h
    rcases hz₁_mem with h₁ | h₁
    · rcases hz₂_mem with h₂ | h₂
      · exact M.zeros_distinct (σ.injective (h₁.trans h₂.symm))
      · exact hv₂ (σ.injective (h.trans h₂.symm))
    · exact hv₁ (σ.injective (h.trans h₁.symm))

-- ══════════════════════════════════════════════════════════════════════
-- Step 1: Specialise to N=5 with HasICP. σ fixes M.sec.
-- ══════════════════════════════════════════════════════════════════════

/-- At N=5 with HasICP, every automorphism fixes the unique non-classifier `M.sec`. -/
private theorem N5_aut_fixes_sec
    (M : DichotomicRetractMagma 5)
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂)
    (σ : Equiv.Perm (Fin 5))
    (h_hom : ∀ a b : Fin 5, σ (M.dot a b) = M.dot (σ a) (σ b)) :
    σ M.sec = M.sec := by
  have h_sec_nc : IsNonClassifier M M.sec := sec_is_non_classifier M
  have h_σsec_nc : IsNonClassifier M (σ M.sec) :=
    aut_preserves_non_classifier M σ h_hom h_sec_nc
  exact unique_non_classifier_at_N5 M hC h_σsec_nc h_sec_nc

-- ══════════════════════════════════════════════════════════════════════
-- Step 2: Strengthened ICP-triple extraction (also returns `hpres`, `hfact`)
-- ══════════════════════════════════════════════════════════════════════

/-- Strengthened version of `N5_icp_triple_structure`: returns the C-triple
    `(τ₁, g, τ₂)` together with the underlying `hpres` (g preserves core)
    and `hfact` (factorisation `τ₁ · x = τ₂ · (g · x)` on core). -/
private theorem N5_icp_triple_full
    (M : DichotomicRetractMagma 5)
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂) :
    ∃ τ₁ g τ₂ : Fin 5,
      τ₁ ≠ g ∧ τ₁ ≠ τ₂ ∧ g ≠ τ₂ ∧
      IsClassifier M τ₁ ∧ IsClassifier M τ₂ ∧
      g = M.sec ∧
      (∀ x : Fin 5, x ≠ M.zero₁ → x ≠ M.zero₂ →
        M.dot g x ≠ M.zero₁ ∧ M.dot g x ≠ M.zero₂) ∧
      (∀ x : Fin 5, x ≠ M.zero₁ → x ≠ M.zero₂ →
        M.dot τ₁ x = M.dot τ₂ (M.dot g x)) := by
  obtain ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
          hpres, hfact, _hnont⟩ := hC
  -- Re-derive what N5_icp_triple_structure proves, but for these names so we
  -- can return hpres and hfact alongside.
  have hcoh := h_triple_coherence M ha1 ha2 hb1 hb2 hc1 hc2 hpres hfact
  -- b is core-preserving, hence a non-classifier.
  have hb_nc : IsNonClassifier M b := by
    refine ⟨hb1, hb2, ?_⟩
    intro x hx1 hx2
    rcases hpres x with h | h | h
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h
  have hb_eq_sec : b = M.sec :=
    unique_non_classifier_at_N5 M
      ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, hpres, hfact, _hnont⟩
      hb_nc (sec_is_non_classifier M)
  -- a, c are classifiers (the non-classifier branch of hcoh would force
  -- two distinct non-classifiers, contradicting uniqueness).
  have ha_cls : IsClassifier M a := by
    rcases hcoh with ⟨ha_cls, _⟩ | ⟨ha_nc, hc_nc⟩
    · exact ha_cls
    · exfalso
      have h_eq := unique_non_classifier_at_N5 M
        ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, hpres, hfact, _hnont⟩
        ha_nc hc_nc
      exact hac h_eq
  have hc_cls : IsClassifier M c := by
    rcases hcoh with ⟨_, hc_cls⟩ | ⟨ha_nc, hc_nc⟩
    · exact hc_cls
    · exfalso
      have h_eq := unique_non_classifier_at_N5 M
        ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, hpres, hfact, _hnont⟩
        ha_nc hc_nc
      exact hac h_eq
  -- Repackage hpres and hfact as conditional implications on core.
  have hpres_core : ∀ x : Fin 5, x ≠ M.zero₁ → x ≠ M.zero₂ →
      M.dot b x ≠ M.zero₁ ∧ M.dot b x ≠ M.zero₂ := by
    intro x hx1 hx2
    rcases hpres x with h | h | h
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h
  have hfact_core : ∀ x : Fin 5, x ≠ M.zero₁ → x ≠ M.zero₂ →
      M.dot a x = M.dot c (M.dot b x) := by
    intro x hx1 hx2
    rcases hfact x with h | h | h
    · exact absurd h hx1
    · exact absurd h hx2
    · exact h
  exact ⟨a, b, c, hab, hac, hbc, ha_cls, hc_cls, hb_eq_sec, hpres_core, hfact_core⟩

-- ══════════════════════════════════════════════════════════════════════
-- Step 3: Main theorem — σ fixes both absorbers
-- ══════════════════════════════════════════════════════════════════════

/-- **Mirror-Row Theorem.** Every automorphism of a DichotomicRetractMagma on
    `Fin 5` with `HasICP` fixes both absorbers.

    Proof: assume σ swaps the absorbers (`σ z₁ = z₂`). Case-split on σ's
    action on the two classifiers (Klein-four sub-case analysis).

    * Case A — σ fixes both classifiers. Pick the classifier `τ₁`. Then
      `τ₁ · τ₁ ∈ Z` and σ-fixed; but σ swaps Z. Contradiction.
    * Case B — σ swaps the two classifiers. C-triple factorisation gives
      `τ₁ · g = τ₂ · (g · g)`. Since σ fixes g (unique non-classifier),
      g · g = g (only σ-fixed core element). So `τ₁ · g = τ₂ · g =: v ∈ Z`,
      and `σ(τ₁ · g) = τ₂ · g = v`, so σ fixes v ∈ Z. But σ swaps Z. -/
theorem N5_aut_preserves_absorbers
    (M : DichotomicRetractMagma 5)
    (hC : HasICP 5 M.dot M.zero₁ M.zero₂)
    (σ : Equiv.Perm (Fin 5))
    (h_hom : ∀ a b : Fin 5, σ (M.dot a b) = M.dot (σ a) (σ b)) :
    σ M.zero₁ = M.zero₁ ∧ σ M.zero₂ = M.zero₂ := by
  -- Reduce to proving σ z₁ = z₁; the second component then follows by injectivity.
  suffices h₁ : σ M.zero₁ = M.zero₁ by
    refine ⟨h₁, ?_⟩
    rcases aut_zero₂_mem M σ h_hom with h | h
    · exact absurd (σ.injective (h.trans h₁.symm)) (Ne.symm M.zeros_distinct)
    · exact h
  -- Suppose for contradiction that σ does NOT fix z₁.
  by_contra hσz₁_ne
  have h_swap₁ : σ M.zero₁ = M.zero₂ := by
    rcases aut_zero₁_mem M σ h_hom with h | h
    · exact absurd h hσz₁_ne
    · exact h
  have h_swap₂ : σ M.zero₂ = M.zero₁ := by
    rcases aut_zero₂_mem M σ h_hom with h | h
    · exact h
    · exact absurd (σ.injective (h_swap₁.trans h.symm)) M.zeros_distinct
  -- σ fixes M.sec.
  have hσg : σ M.sec = M.sec := N5_aut_fixes_sec M hC σ h_hom
  -- Extract the ICP triple and the underlying core lemmas.
  obtain ⟨τ₁, g, τ₂, _hτ₁g, hτ₁τ₂, _hgτ₂, hτ₁_cls, hτ₂_cls, hg_eq_sec,
          hpres_core, hfact_core⟩ := N5_icp_triple_full M hC
  -- Use g = M.sec to get σ g = g.
  have hσg' : σ g = g := by rw [hg_eq_sec]; exact hσg
  -- Both classifiers are non-zero in core.
  obtain ⟨hτ₁_ne₁, hτ₁_ne₂, hτ₁_row⟩ := hτ₁_cls
  obtain ⟨hτ₂_ne₁, hτ₂_ne₂, hτ₂_row⟩ := hτ₂_cls
  -- σ τ₁ is a classifier (preservation lemma); similarly σ τ₂.
  have hστ₁_cls : IsClassifier M (σ τ₁) :=
    aut_preserves_classifier M σ h_hom ⟨hτ₁_ne₁, hτ₁_ne₂, hτ₁_row⟩
  have hστ₂_cls : IsClassifier M (σ τ₂) :=
    aut_preserves_classifier M σ h_hom ⟨hτ₂_ne₁, hτ₂_ne₂, hτ₂_row⟩
  -- σ τ_i is a classifier ≠ M.sec (M.sec is the unique non-classifier).
  -- We will need: σ τ₁ ∈ {τ₁, τ₂} and similarly σ τ₂. To get this, use the fact
  -- that τ₁ and τ₂ are the only two classifiers in core (= {τ₁, τ₂, g} at N=5).
  -- Actually we need a more direct fact: the carrier is {z₁, z₂, τ₁, g, τ₂}
  -- (five distinct elements). σ τ_i is in core (not z₁, z₂) and not g (since
  -- σ τ_i is a classifier and g is the non-classifier).
  -- So σ τ_i ∈ {τ₁, τ₂}.
  -- First, we need τ₁ ≠ g, τ₂ ≠ g (classifier vs non-classifier).
  have hg_nc : IsNonClassifier M g := by
    rw [hg_eq_sec]; exact sec_is_non_classifier M
  have hτ₁_ne_g : τ₁ ≠ g := fun h =>
    classifier_not_non_classifier M τ₁ ⟨hτ₁_ne₁, hτ₁_ne₂, hτ₁_row⟩ (h ▸ hg_nc)
  have hτ₂_ne_g : τ₂ ≠ g := fun h =>
    classifier_not_non_classifier M τ₂ ⟨hτ₂_ne₁, hτ₂_ne₂, hτ₂_row⟩ (h ▸ hg_nc)
  -- The carrier coverage.
  have hg_ne₁ : g ≠ M.zero₁ := hg_nc.1
  have hg_ne₂ : g ≠ M.zero₂ := hg_nc.2.1
  -- Symmetric forms for `simp [Finset.mem_insert]` matching.
  have h12 : M.zero₁ ≠ M.zero₂ := M.zeros_distinct
  have h1τ₁ : M.zero₁ ≠ τ₁ := Ne.symm hτ₁_ne₁
  have h1g : M.zero₁ ≠ g := Ne.symm hg_ne₁
  have h1τ₂ : M.zero₁ ≠ τ₂ := Ne.symm hτ₂_ne₁
  have h2τ₁ : M.zero₂ ≠ τ₁ := Ne.symm hτ₁_ne₂
  have h2g : M.zero₂ ≠ g := Ne.symm hg_ne₂
  have h2τ₂ : M.zero₂ ≠ τ₂ := Ne.symm hτ₂_ne₂
  have hgτ₂ : g ≠ τ₂ := Ne.symm hτ₂_ne_g
  have h_cover : ({M.zero₁, M.zero₂, τ₁, g, τ₂} : Finset (Fin 5)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h1 : M.zero₁ ∉ ({M.zero₂, τ₁, g, τ₂} : Finset (Fin 5)) := by
      simp [h12, h1τ₁, h1g, h1τ₂]
    have h2 : M.zero₂ ∉ ({τ₁, g, τ₂} : Finset (Fin 5)) := by
      simp [h2τ₁, h2g, h2τ₂]
    have h3 : τ₁ ∉ ({g, τ₂} : Finset (Fin 5)) := by
      simp [hτ₁_ne_g, hτ₁τ₂]
    have h4 : g ∉ ({τ₂} : Finset (Fin 5)) := by
      simp [hgτ₂]
    rw [show ({M.zero₁, M.zero₂, τ₁, g, τ₂} : Finset (Fin 5)) =
            insert M.zero₁ (insert M.zero₂ (insert τ₁ (insert g {τ₂}))) from rfl,
        Finset.card_insert_of_notMem h1,
        Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3,
        Finset.card_insert_of_notMem h4,
        Finset.card_singleton, Fintype.card_fin]
  -- Helper: classify any element of core (≠ z₁, z₂) as one of τ₁, g, τ₂.
  have classify_core : ∀ z : Fin 5, z ≠ M.zero₁ → z ≠ M.zero₂ →
      z = τ₁ ∨ z = g ∨ z = τ₂ := by
    intro z hz1 hz2
    have hmem : z ∈ ({M.zero₁, M.zero₂, τ₁, g, τ₂} : Finset (Fin 5)) := by
      rw [h_cover]; exact Finset.mem_univ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exact absurd h hz1
    · exact absurd h hz2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- σ τ₁ is a classifier in core, so σ τ₁ ∈ {τ₁, τ₂} (g is excluded as non-classifier).
  have hστ₁_eq : σ τ₁ = τ₁ ∨ σ τ₁ = τ₂ := by
    rcases classify_core (σ τ₁) hστ₁_cls.1 hστ₁_cls.2.1 with h | h | h
    · exact Or.inl h
    · exfalso
      exact classifier_not_non_classifier M (σ τ₁) hστ₁_cls (h ▸ hg_nc)
    · exact Or.inr h
  have hστ₂_eq : σ τ₂ = τ₁ ∨ σ τ₂ = τ₂ := by
    rcases classify_core (σ τ₂) hστ₂_cls.1 hστ₂_cls.2.1 with h | h | h
    · exact Or.inl h
    · exfalso
      exact classifier_not_non_classifier M (σ τ₂) hστ₂_cls (h ▸ hg_nc)
    · exact Or.inr h
  -- Case split on σ τ₁.
  rcases hστ₁_eq with hστ₁ | hστ₁
  · -- Case A: σ τ₁ = τ₁. Then by injectivity σ τ₂ ≠ τ₁, so σ τ₂ = τ₂.
    have hστ₂ : σ τ₂ = τ₂ := by
      rcases hστ₂_eq with h | h
      · exfalso; apply hτ₁τ₂; exact σ.injective (hστ₁.trans h.symm)
      · exact h
    -- Lemma A: τ₁ · τ₁ ∈ Z and is σ-fixed; but σ swaps Z. Contradiction.
    have h_diag : M.dot τ₁ τ₁ = M.zero₁ ∨ M.dot τ₁ τ₁ = M.zero₂ :=
      hτ₁_row τ₁ hτ₁_ne₁ hτ₁_ne₂
    have h_σ_diag : σ (M.dot τ₁ τ₁) = M.dot τ₁ τ₁ := by
      rw [h_hom, hστ₁]
    rcases h_diag with hd | hd
    · rw [hd] at h_σ_diag
      -- σ z₁ = z₁, but σ z₁ = z₂. Contradiction.
      exact M.zeros_distinct (h_σ_diag.symm.trans h_swap₁)
    · rw [hd] at h_σ_diag
      -- σ z₂ = z₂, but σ z₂ = z₁. Contradiction.
      exact M.zeros_distinct.symm (h_σ_diag.symm.trans h_swap₂)
  · -- Case B: σ τ₁ = τ₂. Then σ τ₂ = τ₁ (by injectivity, the only other option).
    have hστ₂ : σ τ₂ = τ₁ := by
      rcases hστ₂_eq with h | h
      · exact h
      · exfalso; apply hτ₁τ₂; exact σ.injective (hστ₁.trans h.symm)
    -- Step B.1: g · g = g.
    -- g is core-preserving, so g · g is in core, hence in {τ₁, g, τ₂}.
    have hgg_core : M.dot g g ≠ M.zero₁ ∧ M.dot g g ≠ M.zero₂ :=
      hpres_core g hg_ne₁ hg_ne₂
    have hgg_cases : M.dot g g = τ₁ ∨ M.dot g g = g ∨ M.dot g g = τ₂ :=
      classify_core (M.dot g g) hgg_core.1 hgg_core.2
    -- σ fixes g · g.
    have h_σ_gg : σ (M.dot g g) = M.dot g g := by
      rw [h_hom, hσg']
    -- So g · g must be σ-fixed; among {τ₁, g, τ₂}, σ fixes only g.
    have hgg_eq_g : M.dot g g = g := by
      rcases hgg_cases with h | h | h
      · -- g · g = τ₁: σ τ₁ = τ₁, but σ τ₁ = τ₂ and τ₁ ≠ τ₂.
        exfalso
        rw [h] at h_σ_gg
        -- h_σ_gg : σ τ₁ = τ₁; but hστ₁ : σ τ₁ = τ₂.
        exact hτ₁τ₂ (h_σ_gg.symm.trans hστ₁)
      · exact h
      · exfalso
        rw [h] at h_σ_gg
        -- h_σ_gg : σ τ₂ = τ₂; but hστ₂ : σ τ₂ = τ₁.
        exact hτ₁τ₂.symm (h_σ_gg.symm.trans hστ₂)
    -- Step B.2: τ₁ · g = τ₂ · g.
    have h_fact_g : M.dot τ₁ g = M.dot τ₂ (M.dot g g) := hfact_core g hg_ne₁ hg_ne₂
    -- Substitute g · g = g.
    rw [hgg_eq_g] at h_fact_g
    -- h_fact_g : τ₁ · g = τ₂ · g.
    -- Step B.3: v := τ₁ · g ∈ Z (classifier on core).
    have hv_Z : M.dot τ₁ g = M.zero₁ ∨ M.dot τ₁ g = M.zero₂ :=
      hτ₁_row g hg_ne₁ hg_ne₂
    -- Apply σ to τ₁ · g: σ(τ₁ · g) = τ₂ · g = τ₁ · g (= v).
    have h_σ_v : σ (M.dot τ₁ g) = M.dot τ₁ g := by
      rw [h_hom, hστ₁, hσg', ← h_fact_g]
    -- But v ∈ Z and σ swaps Z.
    rcases hv_Z with hv | hv
    · rw [hv] at h_σ_v
      -- σ z₁ = z₁, but σ z₁ = z₂.
      exact M.zeros_distinct (h_σ_v.symm.trans h_swap₁)
    · rw [hv] at h_σ_v
      exact M.zeros_distinct.symm (h_σ_v.symm.trans h_swap₂)

end Dichotomic

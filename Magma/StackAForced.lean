import Magma.ArtifactN8

/-!
# The Stack A Frame, Derived

Two of the artifact's design choices become theorems. Stack A chose
the **swap world** and the size **N = 8**; this file derives both from
two semantic requirements:

* **R1 (observable quotation)**: the introspective classifier answers
  differently on `x` and `quote ⬝ x` — introspection can actually
  *see* quoting. (Without R1, "homoiconic introspection" is blind to
  the one operation homoiconicity is about.)
* **R2 (a hygiene operator)**: there is a faithful core operator
  distinct from quote and from eval — the seed of renaming.

Results:

* `swap_of_observable_quotation` — R1 forces the class-swapping
  world: by the sorted involution theorem the world is preserving or
  swapping, and the determination theorems make preserving worlds
  quote-transparent, contradicting R1.
* `faithful_is_operator` — a faithful element cannot live on the
  classifier side (two absorber values cannot injectively receive
  three core elements), so R2's operator lands in the operator block,
  joining quote and eval.
* `stack_a_frame_min` — the frame (dichotomy + sorting + anchored
  retraction + R1 + R2, with quote, eval, shift pairwise distinct)
  forces **n ≥ 8**: three distinct operators, swap balance forces as
  many classifiers, plus the two absorbers.
* `stack_a_frame_attained` — the canonical artifact satisfies the
  whole frame at n = 8, so the bound is sharp.

What remains *chosen* after this file: the hygiene equations
themselves (commutation, involution), judge-closure, and the lex-min
tie-break. The residue of arbitrariness shrinks; what shrank is now
labeled theorem rather than choice.
-/

set_option autoImplicit false

namespace Dichotomic

/-- **R1 forces the swap world.** In a sorted dichotomic magma with a
    classifier, a non-classifier, and a retraction pair, an
    introspective classifier that observes quotation (answers
    differently on `x` and `s ⬝ x`) is only possible in the
    class-swapping world. -/
theorem swap_of_observable_quotation (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (n₀ : Fin n) (hn1 : n₀ ≠ z₁) (hn2 : n₀ ≠ z₂) (hn₀N : NclSide n dot z₁ z₂ n₀)
    (s r : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hr1 : r ≠ z₁) (hr2 : r ≠ z₂)
    (hsN : NclSide n dot z₁ z₂ s) (hrN : NclSide n dot z₁ z₂ r)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x)
    (hsort : Sorted n dot z₁ z₂)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ)
    (hobs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) ≠ dot κ x) :
    ClassSwapping n dot z₁ z₂ := by
  rcases sorted_involution n dot z₁ z₂ hdich τ hτ1 hτ2 hτC n₀ hn1 hn2 hn₀N
      s r hs1 hs2 hr1 hr2 hsN hrN hrs hsort with hpres | hswap
  · exact absurd hobs
      (no_negating_introspection_of_preserving n dot z₁ z₂ hdich hpres
        s hs1 hs2 hsN κ hκ)
  · exact hswap

/-- **Faithfulness places an element in the operator block.** A core
    element injective on the core cannot be a classifier once the core
    has three distinct elements: two absorber values cannot receive
    three core elements injectively. -/
theorem faithful_is_operator (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (γ : Fin n) (hγ1 : γ ≠ z₁) (hγ2 : γ ≠ z₂)
    (hfaith : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot γ x = dot γ y → x = y)
    (a b c : Fin n)
    (ha1 : a ≠ z₁) (ha2 : a ≠ z₂) (hb1 : b ≠ z₁) (hb2 : b ≠ z₂)
    (hc1 : c ≠ z₁) (hc2 : c ≠ z₂)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    NclSide n dot z₁ z₂ γ := by
  rcases hdich γ with h | h | h | h
  · exact absurd h hγ1
  · exact absurd h hγ2
  · exfalso
    have hva : dot γ a = z₁ ∨ dot γ a = z₂ :=
      ((h a).resolve_left ha1).resolve_left ha2
    have hvb : dot γ b = z₁ ∨ dot γ b = z₂ :=
      ((h b).resolve_left hb1).resolve_left hb2
    have hvc : dot γ c = z₁ ∨ dot γ c = z₂ :=
      ((h c).resolve_left hc1).resolve_left hc2
    rcases hva with ha | ha <;> rcases hvb with hb | hb <;>
      rcases hvc with hc | hc
    all_goals first
      | exact hab (hfaith a b ha1 ha2 hb1 hb2 (ha.trans hb.symm))
      | exact hac (hfaith a c ha1 ha2 hc1 hc2 (ha.trans hc.symm))
      | exact hbc (hfaith b c hb1 hb2 hc1 hc2 (hb.trans hc.symm))
  · exact h

/-- **The frame forces n ≥ 8.** Dichotomy + sorting + an anchored
    retraction pair (quote, eval) + observable quotation (R1) + a
    faithful third operator (R2), with quote, eval, and shift pairwise
    distinct, admit no model below n = 8: the three operators are
    distinct non-classifiers, R1 forces the swap world, swap balance
    forces at least three classifiers, and the two absorbers complete
    the count. -/
theorem stack_a_frame_min (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) (hz : z₁ ≠ z₂)
    (hdich : ∀ y : Fin n, y = z₁ ∨ y = z₂ ∨
      ClsSide n dot z₁ z₂ y ∨ NclSide n dot z₁ z₂ y)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (s r : Fin n) (hs1 : s ≠ z₁) (hs2 : s ≠ z₂) (hr1 : r ≠ z₁) (hr2 : r ≠ z₂)
    (hsN : NclSide n dot z₁ z₂ s) (hrN : NclSide n dot z₁ z₂ r)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x)
    (hsort : Sorted n dot z₁ z₂)
    (κ : Fin n) (hκ : SortIntrospection n dot z₁ z₂ κ)
    (hobs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot κ (dot s x) ≠ dot κ x)
    (γ : Fin n) (hγ1 : γ ≠ z₁) (hγ2 : γ ≠ z₂)
    (hfaith : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot γ x = dot γ y → x = y)
    (hsr : s ≠ r) (hsγ : s ≠ γ) (hrγ : r ≠ γ) :
    8 ≤ n := by
  -- R2's operator is a non-classifier (pigeonhole against s, r, γ)
  have hγN : NclSide n dot z₁ z₂ γ :=
    faithful_is_operator n dot z₁ z₂ hdich γ hγ1 hγ2 hfaith
      s r γ hs1 hs2 hr1 hr2 hγ1 hγ2 hsr hsγ hrγ
  -- R1 forces the swap world (γ serves as the non-classifier witness)
  have hswap : ClassSwapping n dot z₁ z₂ :=
    swap_of_observable_quotation n dot z₁ z₂ hdich τ hτ1 hτ2 hτC
      γ hγ1 hγ2 hγN s r hs1 hs2 hr1 hr2 hsN hrN hrs hsort κ hκ hobs
  -- swap balance: as many classifiers as non-classifiers
  have hbal := swap_balance n dot z₁ z₂ hswap s r hs1 hs2 hsN hrs
  set Cset := Finset.univ.filter (fun y : Fin n =>
    y ≠ z₁ ∧ y ≠ z₂ ∧ ClsSide n dot z₁ z₂ y) with hCdef
  set Nset := Finset.univ.filter (fun y : Fin n =>
    y ≠ z₁ ∧ y ≠ z₂ ∧ NclSide n dot z₁ z₂ y) with hNdef
  -- three distinct non-classifiers
  have hsub : ({s, r, γ} : Finset (Fin n)) ⊆ Nset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs1, hs2, hsN⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1, hr2, hrN⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ1, hγ2, hγN⟩
  have hcard3 : ({s, r, γ} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨s, r, γ, hsr, hsγ, hrγ, rfl⟩
  have hN3 : 3 ≤ Nset.card := by
    calc 3 = ({s, r, γ} : Finset (Fin n)).card := hcard3.symm
      _ ≤ Nset.card := Finset.card_le_card hsub
  -- the classes are disjoint and avoid the absorbers
  have hdisj : Disjoint Cset Nset := by
    rw [Finset.disjoint_left]
    intro y hyC hyN
    simp only [hCdef, Finset.mem_filter] at hyC
    simp only [hNdef, Finset.mem_filter] at hyN
    obtain ⟨-, hy1, hy2, hyCs⟩ := hyC
    obtain ⟨-, -, -, hyNs⟩ := hyN
    -- evaluate both at the core element s
    rcases (hyCs s).resolve_left hs1 |>.resolve_left hs2 with h | h
    · exact ((hyNs s).resolve_left hs1 |>.resolve_left hs2).1 h
    · exact ((hyNs s).resolve_left hs1 |>.resolve_left hs2).2 h
  have hsubU : Cset ∪ Nset ⊆ Finset.univ \ ({z₁, z₂} : Finset (Fin n)) := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · simp only [hCdef, Finset.mem_filter] at h
      simp [Finset.mem_sdiff, h.2.1, h.2.2.1]
    · simp only [hNdef, Finset.mem_filter] at h
      simp [Finset.mem_sdiff, h.2.1, h.2.2.1]
  have hcount : Cset.card + Nset.card ≤ n - 2 := by
    have h1 : (Cset ∪ Nset).card = Cset.card + Nset.card :=
      Finset.card_union_of_disjoint hdisj
    have h2 : (Finset.univ \ ({z₁, z₂} : Finset (Fin n))).card = n - 2 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, Finset.card_pair hz]
    calc Cset.card + Nset.card = (Cset ∪ Nset).card := h1.symm
      _ ≤ (Finset.univ \ ({z₁, z₂} : Finset (Fin n))).card :=
          Finset.card_le_card hsubU
      _ = n - 2 := h2
  -- |C| = |N| ≥ 3, so n - 2 ≥ 6
  omega

/-- **Sharpness**: the canonical artifact satisfies the entire frame
    at n = 8 — sorted, swap world, introspection with observable
    quotation, and a faithful shift distinct from quote and eval. -/
theorem stack_a_frame_attained :
    Sorted 8 dotA8 0 1 ∧ ClassSwapping 8 dotA8 0 1 ∧
    SortIntrospection 8 dotA8 0 1 5 ∧
    (∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 5 (dotA8 2 x) ≠ dotA8 5 x) ∧
    (∀ x y : Fin 8, x ≠ 0 → x ≠ 1 → y ≠ 0 → y ≠ 1 →
      dotA8 4 x = dotA8 4 y → x = y) :=
  ⟨artifactA8_sorted, artifactA8_swapping, artifactA8_introspection,
    artifactA8_negation, artifactA8_shift_faithful⟩

end Dichotomic

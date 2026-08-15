import Magma.Sorting

/-!
# The swap world at every even size

The class-swapping world exists at every admissible carrier size: for
every `m ≥ 2` there is a sorted, class-swapping S+D+C magma on
`2m + 2` elements — two absorbers, `m` operators, `m` judges — with
an anchored mutual retraction pair, the dichotomy, and the internal
composition property (`swap_world_all_even`). Together with
`swap_even_core` (the core of a swap-world magma has even size) this
closes the swap world's size spectrum: the `N = 6` witness `swap6`
becomes the `m = 2` instance of a uniform family.

The family: operators `2..m+1` all act as the block-swap involution
`v ↦ v ± m` on the core (distinguished from one another by their tags
at the `z₂` column); judge `m+2` is the sort introspector χ (accepts
the operator block), judge `m+3` is its complement (accepts the judge
block) — which *is* `χ ∘ swap`, so the ICP triple
`(m+3, 2, m+2)` realizes internal composition, exactly as `judge? =
data? ∘ quote` does in the canonical artifact; the remaining judges
`m+4..2m+1` are the indicator rows of their partner operators. Quote
is operator 2, eval is operator 3; their mutual retraction is the
involution squared.

All proofs are uniform in `m`: row lemmas by `split_ifs`/`omega` over
the raw table, no `decide`.
-/

set_option autoImplicit false

namespace Dichotomic
namespace SwapWorldAllN

/-- The raw table. Rows: `0, 1` absorbers; `2..m+1` operators
    (block-swap on core, tag at column 1); `m+2` the introspector χ;
    `m+3` its complement; `m+4..2m+1` indicator judges. -/
def rawDot (m a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a ≤ m + 1 then
    if b = 0 then 0
    else if b = 1 then a
    else if b ≤ m + 1 then b + m else b - m
  else if a = m + 2 then
    if 2 ≤ b ∧ b ≤ m + 1 then 1 else 0
  else if a = m + 3 then
    if m + 2 ≤ b then 1 else 0
  else
    if b = a - m then 1 else 0

theorem rawDot_lt (m a b : Nat) (ha : a < 2*m+2) (_hb : b < 2*m+2) :
    rawDot m a b < 2*m+2 := by
  unfold rawDot
  split_ifs <;> omega

/-- The table, on `Fin (2m+2)`. -/
def dotS (m : Nat) (a b : Fin (2*m+2)) : Fin (2*m+2) :=
  ⟨rawDot m a.val b.val, rawDot_lt m a.val b.val a.isLt b.isLt⟩

@[simp] theorem dotS_val (m : Nat) (a b : Fin (2*m+2)) :
    (dotS m a b).val = rawDot m a.val b.val := rfl

def zOne (m : Nat) : Fin (2*m+2) := ⟨0, by omega⟩
def zTwo (m : Nat) : Fin (2*m+2) := ⟨1, by omega⟩

@[simp] theorem zOne_val (m : Nat) : (zOne m).val = 0 := rfl
@[simp] theorem zTwo_val (m : Nat) : (zTwo m).val = 1 := rfl

private theorem fin_ne_iff {k : Nat} {a b : Fin k} :
    a ≠ b ↔ a.val ≠ b.val := by
  constructor
  · intro h hv; exact h (Fin.ext hv)
  · intro h he; exact h (congrArg Fin.val he)

-- ═══════════════════════════════════════════════════════════════════
-- Row lemmas (each single-level: split_ifs + omega)
-- ═══════════════════════════════════════════════════════════════════

theorem raw_z1 (m b : Nat) : rawDot m 0 b = 0 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_z2 (m b : Nat) : rawDot m 1 b = 1 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_op_c0 (m a : Nat) (h2 : 2 ≤ a) (hm : a ≤ m+1) :
    rawDot m a 0 = 0 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_op_c1 (m a : Nat) (h2 : 2 ≤ a) (hm : a ≤ m+1) :
    rawDot m a 1 = a := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_op_lo (m a b : Nat) (h2 : 2 ≤ a) (hm : a ≤ m+1)
    (hb2 : 2 ≤ b) (hbm : b ≤ m+1) : rawDot m a b = b + m := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_op_hi (m a b : Nat) (h2 : 2 ≤ a) (hm : a ≤ m+1)
    (hbm : m+2 ≤ b) : rawDot m a b = b - m := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_chi_hit (m b : Nat) (hb2 : 2 ≤ b) (hbm : b ≤ m+1) :
    rawDot m (m+2) b = 1 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_chi_miss (m b : Nat) (hb : ¬ (2 ≤ b ∧ b ≤ m+1)) :
    rawDot m (m+2) b = 0 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_cochi_hit (m b : Nat) (hm : 2 ≤ m) (hb : m+2 ≤ b) :
    rawDot m (m+3) b = 1 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_cochi_miss (m b : Nat) (hm : 2 ≤ m) (hb : b < m+2) :
    rawDot m (m+3) b = 0 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_ind_hit (m a : Nat) (hj : m+4 ≤ a) :
    rawDot m a (a - m) = 1 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

theorem raw_ind_miss (m a b : Nat) (hj : m+4 ≤ a) (hb : b ≠ a - m) :
    rawDot m a b = 0 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

/-- Operator rows are core-valued on core arguments. -/
theorem raw_op_core (m a b : Nat) (h2 : 2 ≤ a) (hm : a ≤ m+1)
    (hb2 : 2 ≤ b) (hbn : b < 2*m+2) :
    2 ≤ rawDot m a b ∧ rawDot m a b < 2*m+2 := by
  by_cases hb : b ≤ m + 1
  · rw [raw_op_lo m a b h2 hm hb2 hb]; omega
  · rw [raw_op_hi m a b h2 hm (by omega)]; omega

/-- Judge rows answer in the halt channels everywhere. -/
theorem raw_jd_bool (m a b : Nat) (hj : m+2 ≤ a) :
    rawDot m a b = 0 ∨ rawDot m a b = 1 := by
  unfold rawDot; split_ifs <;> first | exact ‹False›.elim | omega

/-- Every judge row hits `1` at some core column. -/
theorem raw_jd_one (m a : Nat) (hm : 2 ≤ m) (hj : m+2 ≤ a)
    (ha : a < 2*m+2) :
    ∃ c : Nat, 2 ≤ c ∧ c < 2*m+2 ∧ rawDot m a c = 1 := by
  by_cases h2 : a = m + 2
  · refine ⟨2, by omega, by omega, ?_⟩
    rw [h2]
    exact raw_chi_hit m 2 (by omega) (by omega)
  by_cases h3 : a = m + 3
  · refine ⟨m+2, by omega, by omega, ?_⟩
    rw [h3]
    exact raw_cochi_hit m (m+2) hm (by omega)
  · exact ⟨a - m, by omega, by omega, raw_ind_hit m a (by omega)⟩

-- ═══════════════════════════════════════════════════════════════════
-- Absorbers, no others, extensionality
-- ═══════════════════════════════════════════════════════════════════

theorem zOne_left (m : Nat) (x : Fin (2*m+2)) :
    dotS m (zOne m) x = zOne m :=
  Fin.ext (raw_z1 m x.val)

theorem zTwo_left (m : Nat) (x : Fin (2*m+2)) :
    dotS m (zTwo m) x = zTwo m :=
  Fin.ext (raw_z2 m x.val)

/-- No other absorbers: every core row moves at the `z₁` column. -/
theorem no_other_zeros (m : Nat) (y : Fin (2*m+2))
    (h1 : y ≠ zOne m) (h2 : y ≠ zTwo m) :
    ∃ x : Fin (2*m+2), dotS m y x ≠ y := by
  rw [fin_ne_iff] at h1 h2
  simp only [zOne_val, zTwo_val] at h1 h2
  have hy := y.isLt
  refine ⟨zOne m, ?_⟩
  rw [fin_ne_iff]
  simp only [dotS_val, zOne_val]
  by_cases hop : y.val ≤ m + 1
  · rw [raw_op_c0 m y.val (by omega) hop]; omega
  · rcases raw_jd_bool m y.val 0 (by omega) with h | h <;> omega

/-- Extensionality: distinct elements have distinct rows. -/
theorem extensional (m : Nat) (hm : 2 ≤ m) (a b : Fin (2*m+2))
    (hne : a ≠ b) : ∃ x : Fin (2*m+2), dotS m a x ≠ dotS m b x := by
  rw [fin_ne_iff] at hne
  have ha := a.isLt
  have hb := b.isLt
  -- helper: a judge row differs from any operator row at column 2
  have jd_op : ∀ (j o : Fin (2*m+2)), m + 2 ≤ j.val → 2 ≤ o.val →
      o.val ≤ m + 1 → ∃ x : Fin (2*m+2), dotS m j x ≠ dotS m o x := by
    intro j o hj ho2 hom
    refine ⟨⟨2, by omega⟩, ?_⟩
    rw [fin_ne_iff]
    simp only [dotS_val]
    have h1 : rawDot m o.val 2 = 2 + m :=
      raw_op_lo m o.val 2 ho2 hom (by omega) (by omega)
    rcases raw_jd_bool m j.val 2 hj with h | h <;> omega
  -- helper: a judge row differs from the z₁ row (all zeros) somewhere
  have jd_z1 : ∀ (j : Fin (2*m+2)), m + 2 ≤ j.val →
      ∃ x : Fin (2*m+2), dotS m j x ≠ dotS m (zOne m) x := by
    intro j hj
    obtain ⟨c, hc2, hcn, hc⟩ := raw_jd_one m j.val hm hj j.isLt
    refine ⟨⟨c, hcn⟩, ?_⟩
    rw [fin_ne_iff]
    simp only [dotS_val, zOne_val]
    rw [raw_z1]
    omega
  -- helper: a judge row differs from the z₂ row (all ones) at column 0
  have jd_z2 : ∀ (j : Fin (2*m+2)), m + 2 ≤ j.val →
      ∃ x : Fin (2*m+2), dotS m j x ≠ dotS m (zTwo m) x := by
    intro j hj
    refine ⟨zOne m, ?_⟩
    rw [fin_ne_iff]
    simp only [dotS_val, zOne_val, zTwo_val]
    rw [raw_z2]
    rcases raw_jd_bool m j.val 0 hj with h | h
    · omega
    · -- judge value 1 at column 0 is impossible: all three kinds give 0
      exfalso
      by_cases h2 : j.val = m + 2
      · rw [h2, raw_chi_miss m 0 (by omega)] at h; omega
      by_cases h3 : j.val = m + 3
      · rw [h3, raw_cochi_miss m 0 hm (by omega)] at h; omega
      · rw [raw_ind_miss m j.val 0 (by omega) (by omega)] at h; omega
  -- helper: two distinct judge rows differ somewhere
  have jd_jd : ∀ (j k : Fin (2*m+2)), m + 2 ≤ j.val → m + 2 ≤ k.val →
      j.val ≠ k.val → ∃ x : Fin (2*m+2), dotS m j x ≠ dotS m k x := by
    intro j k hj hk hjk
    have hjlt := j.isLt
    have hklt := k.isLt
    -- χ vs anything else: column 2 (χ answers 1, the others 0)
    by_cases hj2 : j.val = m + 2
    · refine ⟨⟨2, by omega⟩, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val]
      rw [hj2, raw_chi_hit m 2 (by omega) (by omega)]
      by_cases hk3 : k.val = m + 3
      · rw [hk3, raw_cochi_miss m 2 hm (by omega)]; omega
      · rw [raw_ind_miss m k.val 2 (by omega) (by omega)]; omega
    by_cases hk2 : k.val = m + 2
    · refine ⟨⟨2, by omega⟩, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val]
      rw [hk2, raw_chi_hit m 2 (by omega) (by omega)]
      by_cases hj3 : j.val = m + 3
      · rw [hj3, raw_cochi_miss m 2 hm (by omega)]; omega
      · rw [raw_ind_miss m j.val 2 (by omega) (by omega)]; omega
    -- complement vs indicator: column m+2 (complement 1, indicator 0)
    by_cases hj3 : j.val = m + 3
    · refine ⟨⟨m+2, by omega⟩, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val]
      rw [hj3, raw_cochi_hit m (m+2) hm (by omega),
          raw_ind_miss m k.val (m+2) (by omega) (by omega)]
      omega
    by_cases hk3 : k.val = m + 3
    · refine ⟨⟨m+2, by omega⟩, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val]
      rw [hk3, raw_cochi_hit m (m+2) hm (by omega),
          raw_ind_miss m j.val (m+2) (by omega) (by omega)]
      omega
    -- indicator vs indicator: j's partner column
    · refine ⟨⟨j.val - m, by omega⟩, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val]
      rw [raw_ind_hit m j.val (by omega),
          raw_ind_miss m k.val (j.val - m) (by omega) (by omega)]
      omega
  -- main case split
  by_cases haj : m + 2 ≤ a.val
  · by_cases hbj : m + 2 ≤ b.val
    · exact jd_jd a b haj hbj hne
    · by_cases hb0 : b.val = 0
      · obtain ⟨x, hx⟩ := jd_z1 a haj
        refine ⟨x, ?_⟩
        have : b = zOne m := Fin.ext hb0
        rwa [this]
      by_cases hb1 : b.val = 1
      · obtain ⟨x, hx⟩ := jd_z2 a haj
        refine ⟨x, ?_⟩
        have : b = zTwo m := Fin.ext hb1
        rwa [this]
      · exact jd_op a b haj (by omega) (by omega)
  · by_cases hbj : m + 2 ≤ b.val
    · by_cases ha0 : a.val = 0
      · obtain ⟨x, hx⟩ := jd_z1 b hbj
        refine ⟨x, fun he => hx ?_⟩
        have : a = zOne m := Fin.ext ha0
        rw [← this]
        exact he.symm
      by_cases ha1 : a.val = 1
      · obtain ⟨x, hx⟩ := jd_z2 b hbj
        refine ⟨x, fun he => hx ?_⟩
        have : a = zTwo m := Fin.ext ha1
        rw [← this]
        exact he.symm
      · obtain ⟨x, hx⟩ := jd_op b a hbj (by omega) (by omega)
        exact ⟨x, fun he => hx he.symm⟩
    · -- both in {absorbers, operators}: column 1 carries the tag
      refine ⟨zTwo m, ?_⟩
      rw [fin_ne_iff]
      simp only [dotS_val, zTwo_val]
      have val1 : ∀ v : Nat, v < 2*m+2 → ¬ m + 2 ≤ v →
          rawDot m v 1 = v := by
        intro v hv hvo
        by_cases h0 : v = 0
        · rw [h0, raw_z1]
        · by_cases h1 : v = 1
          · rw [h1, raw_z2]
          · exact raw_op_c1 m v (by omega) (by omega)
      rw [val1 a.val ha haj, val1 b.val hb hbj]
      exact hne

-- ═══════════════════════════════════════════════════════════════════
-- The retraction pair (quote = 2, eval = 3)
-- ═══════════════════════════════════════════════════════════════════

/-- Any operator after any operator is the identity on core: the
    block-swap involution squared. -/
theorem raw_swap_swap (m r s v : Nat) (hr2 : 2 ≤ r) (hrm : r ≤ m+1)
    (hs2 : 2 ≤ s) (hsm : s ≤ m+1) (hv2 : 2 ≤ v) (hvn : v < 2*m+2) :
    rawDot m r (rawDot m s v) = v := by
  by_cases hv : v ≤ m + 1
  · rw [raw_op_lo m s v hs2 hsm hv2 hv,
        raw_op_hi m r (v + m) hr2 hrm (by omega)]
    omega
  · rw [raw_op_hi m s v hs2 hsm (by omega),
        raw_op_lo m r (v - m) hr2 hrm (by omega) (by omega)]
    omega

theorem retract_pair (m : Nat) (hm : 2 ≤ m) :
    HasRetractPair (2*m+2) (dotS m) (zOne m) (zTwo m) := by
  refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ?_, ?_, ?_⟩
  · intro x hx1 hx2
    rw [fin_ne_iff] at hx1 hx2
    simp only [zOne_val, zTwo_val] at hx1 hx2
    exact Fin.ext (raw_swap_swap m 3 2 x.val (by omega) (by omega)
      (by omega) (by omega) (by omega) x.isLt)
  · intro x hx1 hx2
    rw [fin_ne_iff] at hx1 hx2
    simp only [zOne_val, zTwo_val] at hx1 hx2
    exact Fin.ext (raw_swap_swap m 2 3 x.val (by omega) (by omega)
      (by omega) (by omega) (by omega) x.isLt)
  · exact Fin.ext (raw_op_c0 m 3 (by omega) (by omega))

-- ═══════════════════════════════════════════════════════════════════
-- Sides: operators are non-classifiers, judges are classifiers
-- ═══════════════════════════════════════════════════════════════════

theorem op_ncl (m : Nat) (y : Fin (2*m+2)) (h2 : 2 ≤ y.val)
    (hv : y.val ≤ m + 1) :
    NclSide (2*m+2) (dotS m) (zOne m) (zTwo m) y := by
  intro x
  by_cases hx0 : x.val = 0
  · exact Or.inl (Fin.ext hx0)
  by_cases hx1 : x.val = 1
  · exact Or.inr (Or.inl (Fin.ext hx1))
  have hc := raw_op_core m y.val x.val h2 hv (by omega) x.isLt
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · rw [fin_ne_iff]; simp only [dotS_val, zOne_val]; omega
  · rw [fin_ne_iff]; simp only [dotS_val, zTwo_val]; omega

theorem jd_cls (m : Nat) (x : Fin (2*m+2)) (hv : m + 2 ≤ x.val) :
    ClsSide (2*m+2) (dotS m) (zOne m) (zTwo m) x := by
  intro b
  refine Or.inr (Or.inr ?_)
  rcases raw_jd_bool m x.val b.val hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- A core element on the non-classifier side is an operator. -/
theorem ncl_is_op (m : Nat) (hm : 2 ≤ m) (y : Fin (2*m+2))
    (_h1 : y ≠ zOne m) (_h2 : y ≠ zTwo m)
    (hN : NclSide (2*m+2) (dotS m) (zOne m) (zTwo m) y) :
    y.val ≤ m + 1 := by
  have hy := y.isLt
  by_contra hj
  -- y is a judge: at some core column it answers 1 = z₂
  obtain ⟨c, hc2, hcn, hc⟩ := raw_jd_one m y.val hm (by omega) hy
  have hp1 : (⟨c, hcn⟩ : Fin (2*m+2)) ≠ zOne m := by
    rw [fin_ne_iff]; simp only [zOne_val]; omega
  have hp2 : (⟨c, hcn⟩ : Fin (2*m+2)) ≠ zTwo m := by
    rw [fin_ne_iff]; simp only [zTwo_val]; omega
  rcases hN ⟨c, hcn⟩ with h | h | ⟨_, hh2⟩
  · exact hp1 h
  · exact hp2 h
  · exact hh2 (Fin.ext hc)

/-- A core element on the classifier side is a judge. -/
theorem cls_is_jd (m : Nat) (_hm : 2 ≤ m) (x : Fin (2*m+2))
    (h1 : x ≠ zOne m) (h2 : x ≠ zTwo m)
    (hC : ClsSide (2*m+2) (dotS m) (zOne m) (zTwo m) x) :
    m + 2 ≤ x.val := by
  have hx := x.isLt
  rw [fin_ne_iff] at h1 h2
  simp only [zOne_val, zTwo_val] at h1 h2
  by_contra hop
  -- x is an operator: at column 2 it answers 2 + m, which is core
  have hc := raw_op_core m x.val 2 (by omega) (by omega) (by omega)
    (by omega)
  rcases hC ⟨2, by omega⟩ with h | h | h
  · have hv : (2 : Nat) = 0 := congrArg Fin.val h
    omega
  · have hv : (2 : Nat) = 1 := congrArg Fin.val h
    omega
  · rcases h with h | h
    · have hv : rawDot m x.val 2 = 0 := congrArg Fin.val h
      omega
    · have hv : rawDot m x.val 2 = 1 := congrArg Fin.val h
      omega

-- ═══════════════════════════════════════════════════════════════════
-- The dichotomy, the swap, sorting, and the ICP
-- ═══════════════════════════════════════════════════════════════════

theorem dichotomy_pointwise (m : Nat) (y : Fin (2*m+2)) :
    y = zOne m ∨ y = zTwo m ∨
    ClsSide (2*m+2) (dotS m) (zOne m) (zTwo m) y ∨
    NclSide (2*m+2) (dotS m) (zOne m) (zTwo m) y := by
  have hy := y.isLt
  by_cases h0 : y.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : y.val = 1
  · exact Or.inr (Or.inl (Fin.ext h1))
  by_cases hop : y.val ≤ m + 1
  · exact Or.inr (Or.inr (Or.inr (op_ncl m y (by omega) hop)))
  · exact Or.inr (Or.inr (Or.inl (jd_cls m y (by omega))))

theorem has_dichotomy (m : Nat) (hm : 2 ≤ m) :
    HasDichotomy (2*m+2) (dotS m) (zOne m) (zTwo m) := by
  refine ⟨⟨⟨m+2, by omega⟩, ?_, ?_, ?_⟩,
    dichotomy_pointwise m,
    ⟨⟨2, by omega⟩, ?_, ?_, ⟨2, by omega⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · intro b
    rcases raw_jd_bool m (m+2) b.val (by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · rw [fin_ne_iff]
    simp only [dotS_val, zOne_val]
    rw [raw_op_lo m 2 2 (by omega) (by omega) (by omega) (by omega)]
    omega
  · rw [fin_ne_iff]
    simp only [dotS_val, zTwo_val]
    rw [raw_op_lo m 2 2 (by omega) (by omega) (by omega) (by omega)]
    omega

theorem class_swapping (m : Nat) (hm : 2 ≤ m) :
    ClassSwapping (2*m+2) (dotS m) (zOne m) (zTwo m) := by
  intro y x hy1 hy2 hx1 hx2 hyN
  have hyop : y.val ≤ m + 1 := ncl_is_op m hm y hy1 hy2 hyN
  have hy2' : 2 ≤ y.val := by
    rw [fin_ne_iff] at hy1 hy2
    simp only [zOne_val, zTwo_val] at hy1 hy2
    omega
  have hx2' : 2 ≤ x.val := by
    rw [fin_ne_iff] at hx1 hx2
    simp only [zOne_val, zTwo_val] at hx1 hx2
    omega
  have hxlt := x.isLt
  constructor
  · intro hxC
    have hxj : m + 2 ≤ x.val := cls_is_jd m hm x hx1 hx2 hxC
    have hval : (dotS m y x).val = x.val - m :=
      raw_op_hi m y.val x.val hy2' hyop hxj
    exact op_ncl m (dotS m y x) (by omega) (by omega)
  · intro hxN
    have hxop : x.val ≤ m + 1 := ncl_is_op m hm x hx1 hx2 hxN
    have hval : (dotS m y x).val = x.val + m :=
      raw_op_lo m y.val x.val hy2' hyop hx2' hxop
    exact jd_cls m (dotS m y x) (by omega)

theorem sorted (m : Nat) (hm : 2 ≤ m) :
    Sorted (2*m+2) (dotS m) (zOne m) (zTwo m) :=
  sorted_of_swapping (2*m+2) (dotS m) (zOne m) (zTwo m)
    (dichotomy_pointwise m)
    ⟨m+2, by omega⟩
    (by rw [fin_ne_iff]; simp only [zOne_val]; omega)
    (by rw [fin_ne_iff]; simp only [zTwo_val]; omega)
    (jd_cls m ⟨m+2, by omega⟩ (by simp))
    (class_swapping m hm)

/-- **The ICP**: the complement judge is the introspector composed
    with quotation — the triple `(m+3, 2, m+2)` realizes internal
    composition, exactly as `judge? = data? ∘ quote` does in the
    canonical artifact. -/
theorem has_icp (m : Nat) (hm : 2 ≤ m) :
    HasICP (2*m+2) (dotS m) (zOne m) (zTwo m) := by
  refine ⟨⟨m+3, by omega⟩, ⟨2, by omega⟩, ⟨m+2, by omega⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fin_ne_iff]; show m + 3 ≠ 2; omega
  · rw [fin_ne_iff]; show m + 3 ≠ m + 2; omega
  · rw [fin_ne_iff]; show (2 : Nat) ≠ m + 2; omega
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · rw [fin_ne_iff]; simp only [zOne_val]; omega
  · rw [fin_ne_iff]; simp only [zTwo_val]; omega
  · -- quote preserves the core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    have hc := raw_op_core m 2 x.val (by omega) (by omega) (by omega)
      x.isLt
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [fin_ne_iff]; simp only [dotS_val, zOne_val]; omega
    · rw [fin_ne_iff]; simp only [dotS_val, zTwo_val]; omega
  · -- factorization: complement = χ ∘ quote on core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    refine Or.inr (Or.inr (Fin.ext ?_))
    show rawDot m (m+3) x.val = rawDot m (m+2) (rawDot m 2 x.val)
    have hx := x.isLt
    by_cases hop : x.val ≤ m + 1
    · rw [raw_cochi_miss m x.val hm (by omega),
          raw_op_lo m 2 x.val (by omega) (by omega) (by omega) hop,
          raw_chi_miss m (x.val + m) (by omega)]
    · rw [raw_cochi_hit m x.val hm (by omega),
          raw_op_hi m 2 x.val (by omega) (by omega) (by omega),
          raw_chi_hit m (x.val - m) (by omega) (by omega)]
  · -- non-triviality: the complement separates operators from judges
    refine ⟨⟨2, by omega⟩, ⟨m+2, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fin_ne_iff]; simp only [zOne_val]; omega
    · rw [fin_ne_iff]; simp only [zTwo_val]; omega
    · rw [fin_ne_iff]; simp only [zOne_val]; omega
    · rw [fin_ne_iff]; simp only [zTwo_val]; omega
    · rw [fin_ne_iff]
      show rawDot m (m+3) 2 ≠ rawDot m (m+3) (m+2)
      rw [raw_cochi_miss m 2 hm (by omega),
          raw_cochi_hit m (m+2) hm (by omega)]
      omega

-- ═══════════════════════════════════════════════════════════════════
-- The packaged existence theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **The swap world exists at every even size, with the full
    S+D+C stack**: for every `m ≥ 2` there is a magma on `2m + 2`
    elements with two left-absorbers and no others, extensional,
    carrying an anchored mutual retraction pair (S), the dichotomy
    (D), the internal composition property (C), the class-swapping
    law, and sorting. With `swap_even_core` this closes the spectrum:
    the `N = 6` witness `swap6` is the `m = 2` instance of this
    family, and at every odd size the sorted S+D+C landscape is
    confined to the preserving world. -/
theorem swap_world_all_even (m : Nat) (hm : 2 ≤ m) :
    ∃ (dot : Fin (2*m+2) → Fin (2*m+2) → Fin (2*m+2))
      (z₁ z₂ : Fin (2*m+2)),
      z₁ ≠ z₂ ∧
      (∀ x, dot z₁ x = z₁) ∧
      (∀ x, dot z₂ x = z₂) ∧
      (∀ y, y ≠ z₁ → y ≠ z₂ → ∃ x, dot y x ≠ y) ∧
      (∀ a b, a ≠ b → ∃ x, dot a x ≠ dot b x) ∧
      HasRetractPair (2*m+2) dot z₁ z₂ ∧
      HasDichotomy (2*m+2) dot z₁ z₂ ∧
      HasICP (2*m+2) dot z₁ z₂ ∧
      ClassSwapping (2*m+2) dot z₁ z₂ ∧
      Sorted (2*m+2) dot z₁ z₂ :=
  ⟨dotS m, zOne m, zTwo m,
    by rw [fin_ne_iff]; simp,
    zOne_left m, zTwo_left m,
    no_other_zeros m,
    extensional m hm,
    retract_pair m hm,
    has_dichotomy m hm,
    has_icp m hm,
    class_swapping m hm,
    sorted m hm⟩

end SwapWorldAllN
end Dichotomic

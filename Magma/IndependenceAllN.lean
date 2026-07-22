import Magma.Dichotomic
import Magma.ICP
import Magma.E2PM
import Magma.WitnessAllN

/-!
# Witnesses at Every Size: the Independence is Not a Small-Size Artifact

Parametric families of extensional 2-pointed magmas proving that every
capability profile persists at *every* admissible carrier size. This
turns the scaling conjecture (previously supported by SAT search up to
N=15) into a theorem: for all n ≥ 5 (n ≥ 4 where noted), each of the six
non-implications and the triple coexistence S+D+C have witnesses of size
exactly n.

All proofs are algebraic (no `decide` on tables): each family is an
explicitly defined n×n Cayley table whose properties are verified by
symbolic case analysis, uniformly in n.

## Families

| Family | Profile | Sizes | Covers |
|--------|---------------|-------|--------------------------|
| G  | D, ¬S, ¬C | n ≥ 4 | D ⇏ S, D ⇏ C; cube cell 6 |
| E  | S, ¬D, ¬C | n ≥ 5 | S ⇏ C (structurally); cube cell 4 |
| F  | S, ¬D, ¬C | n ≥ 5 | S ⇏ D (non-vacuously: classifier + non-classifier + mixed) |
| Dm | C, ¬S, ¬D | n ≥ 5 | C ⇏ S, C ⇏ D; cube cell 7 |
| Hm | S, D, ¬C  | n ≥ 5 | S+D ⇏ C; cube cell 2 |
| Cm | S, C, ¬D  | n ≥ 5 | S+C ⇏ D; cube cell 3 (improves N=10 → N=5, tight) |
| B  | D, C, ¬S  | n ≥ 5 | D+C ⇏ S; cube cell 5 |
| Z  | ¬S, ¬D, ¬C | n ≥ 4 | cube cell 8 |

Together with the coexistence family of `WitnessAllN.lean` (cube cell 1),
families Hm, Cm, B, G, E, Dm, Z realize *every* cell of the (S, D, C)
Boolean cube at every admissible size (`boolean_cube_all_N`): joint
irredundance is not a small-size artifact either, and no two capabilities
force the third at any size.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Dichotomic
namespace IndependenceAllN

/-- Two explicitly-bounded `Fin` elements with distinct values are distinct. -/
private theorem fin_ne {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)

/-- Close a goal by linear arithmetic, first discharging any literal `False`
    hypothesis left in context by `split_ifs` on decidable literal conditions. -/
local macro "falso_omega" : tactic =>
  `(tactic| first
    | exact False.elim (by assumption)
    | exact absurd rfl (by assumption)
    | omega)

-- ═══════════════════════════════════════════════════════════════════
-- Family G: D ∧ ¬R ∧ ¬H at every n ≥ 4
-- ═══════════════════════════════════════════════════════════════════

/-! Table (elements 0, 1 absorbers):
- row 2: `(0, 1, 1, …, 1)` — a classifier;
- row y ≥ 3: `y·0 = 0`, `y·1 = y`, `y·x = 2` for `x ≥ 2` — non-classifiers,
  constant on core.

¬R: every element satisfies `s·2 = s·3`, so no section can act injectively.
¬H: every core-preserving element is constant (value 2) on the core, so any
factorization forces the composed element to be constant, violating
non-triviality. -/

private def rawG (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then (if b = 0 then 0 else 1)
  else if b = 0 then 0
  else if b = 1 then a
  else 2

private theorem rawG_lt {n : Nat} (hn : 4 ≤ n) (a : Fin n) (b : Nat) :
    rawG a.val b < n := by
  have := a.isLt
  unfold rawG
  split_ifs <;> falso_omega

def dotG (m : Nat) (a b : Fin (m + 4)) : Fin (m + 4) :=
  ⟨rawG a.val b.val, rawG_lt (by omega) a b.val⟩

def famG (m : Nat) : Ext2PointedMagma (m + 4) where
  dot := dotG m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawG y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawG at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h0 : rawG a.val 0 = rawG b.val 0 := congrArg Fin.val (h ⟨0, by omega⟩)
    have h1 : rawG a.val 1 = rawG b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    have h2 : rawG a.val 2 = rawG b.val 2 := congrArg Fin.val (h ⟨2, by omega⟩)
    apply Fin.ext
    unfold rawG at h0 h1 h2
    split_ifs at h0 h1 h2 <;> falso_omega

theorem famG_dichotomy (m : Nat) :
    HasDichotomy (m + 4) (dotG m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩, ?_, ?_⟩
  · -- element 2 is a classifier: boolean on all inputs
    intro x
    rcases Nat.eq_zero_or_pos x.val with hx | hx
    · exact Or.inl (Fin.ext (by show rawG 2 x.val = 0; unfold rawG; split_ifs <;> falso_omega))
    · exact Or.inr (Fin.ext (by show rawG 2 x.val = 1; unfold rawG; split_ifs <;> falso_omega))
  · -- the dichotomy
    intro y
    by_cases hy0 : y.val = 0
    · exact Or.inl (Fin.ext hy0)
    by_cases hy1 : y.val = 1
    · exact Or.inr (Or.inl (Fin.ext hy1))
    by_cases hy2 : y.val = 2
    · -- classifier side
      refine Or.inr (Or.inr (Or.inl fun x => ?_))
      rcases Nat.eq_zero_or_pos x.val with hx | hx
      · exact Or.inl (Fin.ext hx)
      · refine Or.inr (Or.inr ?_)
        rcases Nat.eq_or_lt_of_le hx with hx1 | hx1
        · exact Or.inr (Fin.ext (by show rawG y.val x.val = 1; unfold rawG; split_ifs <;> falso_omega))
        · exact Or.inr (Fin.ext (by show rawG y.val x.val = 1; unfold rawG; split_ifs <;> falso_omega))
    · -- non-classifier side (y ≥ 3)
      refine Or.inr (Or.inr (Or.inr fun x => ?_))
      by_cases hx0 : x.val = 0
      · exact Or.inl (Fin.ext hx0)
      by_cases hx1 : x.val = 1
      · exact Or.inr (Or.inl (Fin.ext hx1))
      · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
        · have h' : rawG y.val x.val = 0 := congrArg Fin.val h
          unfold rawG at h'
          split_ifs at h' <;> falso_omega
        · have h' : rawG y.val x.val = 1 := congrArg Fin.val h
          unfold rawG at h'
          split_ifs at h' <;> falso_omega
  · -- non-degeneracy: 3 · 2 = 2 ∉ {0, 1}
    refine ⟨⟨3, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      ⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fun h => ?_, fun h => ?_⟩
    · have h' : rawG 3 2 = 0 := congrArg Fin.val h
      simp [rawG] at h'
    · have h' : rawG 3 2 = 1 := congrArg Fin.val h
      simp [rawG] at h'

theorem famG_no_retract (m : Nat) :
    ¬ HasRetractPair (m + 4) (dotG m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨s, r, hrs, -, -⟩
  have key : dotG m s ⟨2, by omega⟩ = dotG m s ⟨3, by omega⟩ := by
    apply Fin.ext
    show rawG s.val 2 = rawG s.val 3
    unfold rawG
    split_ifs <;> falso_omega
  have h2 := hrs ⟨2, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  have h3 := hrs ⟨3, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  refine fin_ne (show 2 < m + 4 by omega) (show 3 < m + 4 by omega) (by omega) ?_
  calc (⟨2, by omega⟩ : Fin (m + 4))
      = dotG m r (dotG m s ⟨2, by omega⟩) := h2.symm
    _ = dotG m r (dotG m s ⟨3, by omega⟩) := by rw [key]
    _ = ⟨3, by omega⟩ := h3

theorem famG_no_icp (m : Nat) :
    ¬ HasICP (m + 4) (dotG m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
    hpres, hfact, x, y, hx1, hx2, hy1, hy2, hne⟩
  have hbv : 2 ≤ b.val := by
    have h1 : b.val ≠ 0 := fun h => hb1 (Fin.ext h)
    have h2 : b.val ≠ 1 := fun h => hb2 (Fin.ext h)
    omega
  rcases Nat.eq_or_lt_of_le hbv with hb2v | hb3v
  · -- b = 2 is the classifier: it does not preserve the core (2·2 = 1)
    rcases hpres ⟨2, by omega⟩ with h | h | h
    · exact fin_ne _ _ (by omega) h
    · exact fin_ne _ _ (by omega) h
    · exact h.2 (Fin.ext (by show rawG b.val 2 = 1; unfold rawG; split_ifs <;> falso_omega))
  · -- b ≥ 3 is constant (value 2) on the core, so a is constant on the core
    have hbconst : ∀ t : Fin (m + 4), t.val ≠ 0 → t.val ≠ 1 →
        dotG m b t = ⟨2, by omega⟩ := by
      intro t ht1 ht2
      apply Fin.ext
      show rawG b.val t.val = 2
      unfold rawG
      split_ifs <;> falso_omega
    have hxv1 : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hxv2 : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    have hyv1 : y.val ≠ 0 := fun h => hy1 (Fin.ext h)
    have hyv2 : y.val ≠ 1 := fun h => hy2 (Fin.ext h)
    have hfx := ((hfact x).resolve_left hx1).resolve_left hx2
    have hfy := ((hfact y).resolve_left hy1).resolve_left hy2
    rw [hbconst x hxv1 hxv2] at hfx
    rw [hbconst y hyv1 hyv2] at hfy
    exact hne (hfx.trans hfy.symm)

/-- **D ⇏ S and D ⇏ H at every size n ≥ 4.** -/
theorem d_without_s_c_all_N (n : Nat) (hn : 4 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact ⟨famG m, famG_dichotomy m, famG_no_retract m, famG_no_icp m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family E: R ∧ ¬D ∧ ¬H at every n ≥ 5 (transposition family)
-- ═══════════════════════════════════════════════════════════════════

/-! Table (elements 0, 1 absorbers; all core rows are 0 on the absorber
columns): the core elements act on the core as distinct transpositions,
`L₂ = (3 4)` and `L_y = (2 y)` for y ≥ 3. Every `L_y` is an involution, so
every core element is its own retraction pair. The composition of two
distinct transpositions is never a transposition, so no ICP factorization
exists — ICP fails structurally at every size. Column 2 is the identity
column, giving extensionality for free. -/

private def rawE (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if b = 0 then 0
  else if b = 1 then 0
  else if a = 2 then (if b = 3 then 4 else if b = 4 then 3 else b)
  else if b = 2 then a
  else if b = a then 2
  else b

private theorem rawE_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawE a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawE
  split_ifs <;> falso_omega

def dotE (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawE a.val b.val, rawE_lt (by omega) a b⟩

/-- Column 2 of family E is the identity column (value level). -/
private theorem rawE_col2 (t : Nat) : rawE t 2 = t := by
  unfold rawE
  split_ifs <;> falso_omega

/-- Column 2 of family E is the identity column. -/
private theorem dotE_col2 (m : Nat) (t : Fin (m + 5)) :
    dotE m t ⟨2, by omega⟩ = t :=
  Fin.ext (rawE_col2 t.val)

def famE (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotE m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawE y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawE at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h2 := h ⟨2, by omega⟩
    rw [dotE_col2, dotE_col2] at h2
    exact h2

theorem famE_retract (m : Nat) :
    HasRetractPair (m + 5) (dotE m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have key : ∀ x : Fin (m + 5), x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotE m ⟨2, by omega⟩ (dotE m ⟨2, by omega⟩ x) = x := by
    intro x hx1 hx2
    have hx1' : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hx2' : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    apply Fin.ext
    show rawE 2 (rawE 2 x.val) = x.val
    by_cases h3 : x.val = 3
    · rw [h3]; rfl
    by_cases h4 : x.val = 4
    · rw [h4]; rfl
    · have hin : rawE 2 x.val = x.val := by
        unfold rawE
        split_ifs <;> falso_omega
      rw [hin, hin]
  exact ⟨⟨2, by omega⟩, ⟨2, by omega⟩, key, key, rfl⟩

/-- Family E has no classifier (so ¬D): every core element has a
    core-valued output on the core (its own column-2 value). -/
theorem famE_no_dichotomy (m : Nat) :
    ¬ HasDichotomy (m + 5) (dotE m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨⟨cls, hcz1, hcz2, hbool⟩, -, -⟩
  have hcv0 : cls.val ≠ 0 := fun h => hcz1 (Fin.ext h)
  have hcv1 : cls.val ≠ 1 := fun h => hcz2 (Fin.ext h)
  rcases hbool ⟨2, by omega⟩ with h | h
  · have h' : rawE cls.val 2 = 0 := congrArg Fin.val h
    unfold rawE at h'
    split_ifs at h' <;> falso_omega
  · have h' : rawE cls.val 2 = 1 := congrArg Fin.val h
    unfold rawE at h'
    split_ifs at h' <;> falso_omega

theorem famE_no_icp (m : Nat) :
    ¬ HasICP (m + 5) (dotE m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2, hpres, hfact, -⟩
  have hav0 : a.val ≠ 0 := fun h => ha1 (Fin.ext h)
  have hav1 : a.val ≠ 1 := fun h => ha2 (Fin.ext h)
  have hbv0 : b.val ≠ 0 := fun h => hb1 (Fin.ext h)
  have hbv1 : b.val ≠ 1 := fun h => hb2 (Fin.ext h)
  have hcv0 : c.val ≠ 0 := fun h => hc1 (Fin.ext h)
  have hcv1 : c.val ≠ 1 := fun h => hc2 (Fin.ext h)
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hacv : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbcv : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  by_cases hb2v : b.val = 2
  · -- b acts as (3 4): evaluate the factorization at column 2 — a·2 = c·(b·2) gives a = c
    have h := ((hfact ⟨2, by omega⟩).resolve_left
      (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega))
    have hval : rawE a.val 2 = rawE c.val (rawE b.val 2) := congrArg Fin.val h
    rw [hb2v] at hval
    simp only [rawE_col2] at hval
    exact hacv hval
  · -- b = (2 b): evaluate at column b — a·b = c·(b·b) = c·2 = c
    have hfb : rawE a.val b.val = rawE c.val (rawE b.val b.val) :=
      congrArg Fin.val (((hfact b).resolve_left hb1).resolve_left hb2)
    have hbb : rawE b.val b.val = 2 := by
      unfold rawE
      split_ifs <;> falso_omega
    rw [hbb, rawE_col2] at hfb
    -- hfb : rawE a.val b.val = c.val
    by_cases ha2v : a.val = 2
    · rw [ha2v] at hfb
      by_cases hb3 : b.val = 3
      · -- c = 2·3 = 4; contradiction at column 4: 2·4 = 3 ≠ 4·(3·4) = 4·4 = 2
        rw [hb3] at hfb
        have hc4 : c.val = 4 := hfb.symm
        have h4 : rawE a.val 4 = rawE c.val (rawE b.val 4) :=
          congrArg Fin.val (((hfact ⟨4, by omega⟩).resolve_left
            (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega)))
        rw [ha2v, hb3, hc4] at h4
        have : (3 : Nat) = 2 := h4
        omega
      by_cases hb4 : b.val = 4
      · -- c = 2·4 = 3; contradiction at column 3: 2·3 = 4 ≠ 3·(4·3) = 3·3 = 2
        rw [hb4] at hfb
        have hc3 : c.val = 3 := hfb.symm
        have h3 : rawE a.val 3 = rawE c.val (rawE b.val 3) :=
          congrArg Fin.val (((hfact ⟨3, by omega⟩).resolve_left
            (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega)))
        rw [ha2v, hb4, hc3] at h3
        have : (4 : Nat) = 2 := h3
        omega
      · -- b ≥ 5: 2·b = b, so c = b — contradiction with b ≠ c
        have hval : rawE 2 b.val = b.val := by
          unfold rawE
          split_ifs <;> falso_omega
        rw [hval] at hfb
        exact hbcv hfb
    · -- a ≥ 3, a ≠ b: a·b = b (the transposition (2 a) fixes b), so c = b
      have hval : rawE a.val b.val = b.val := by
        unfold rawE
        split_ifs <;> falso_omega
      rw [hval] at hfb
      exact hbcv hfb

/-- **S ⇏ C (structurally) and S ⇏ D at every size n ≥ 5.** -/
theorem s_without_c_d_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famE m, famE_retract m, famE_no_icp m, famE_no_dichotomy m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family F: R with a *non-vacuous* dichotomy failure at every n ≥ 5
-- ═══════════════════════════════════════════════════════════════════

/-! Table (elements 0, 1 absorbers):
- row 2: identity on core (`2·0 = 0`, `2·1 = 2`, `2·x = x`) — sec = ret,
  a pure non-classifier;
- row 3: classifier (`3·x = 1` iff `x = 3`, else 0);
- row 4: MIXED (`4·2 = 0` but `4·x = 2` for `x ≥ 3`) — violates the dichotomy;
- rows y ≥ 5: `y·0 = 0`, `y·1 = y`, `y·x = 2` — non-classifiers.

R holds, a classifier exists, a pure non-classifier exists, and the
dichotomy fails at the mixed element: the *non-vacuous* S ⇏ D witness,
at every size n ≥ 5. -/

private def rawF (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then (if b = 0 then 0 else if b = 1 then 2 else b)
  else if a = 3 then (if b = 3 then 1 else 0)
  else if a = 4 then (if b ≤ 2 then 0 else 2)
  else if b = 0 then 0
  else if b = 1 then a
  else 2

private theorem rawF_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawF a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawF
  split_ifs <;> falso_omega

def dotF (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawF a.val b.val, rawF_lt (by omega) a b⟩

/-- Row 2 of family F is the identity on the core. -/
private theorem dotF_id (m : Nat) (x : Fin (m + 5))
    (hx0 : x.val ≠ 0) (hx1 : x.val ≠ 1) :
    dotF m ⟨2, by omega⟩ x = x := by
  apply Fin.ext
  show rawF 2 x.val = x.val
  unfold rawF
  split_ifs <;> falso_omega

private theorem rawF_col1 (t : Nat) : rawF t 1 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
    else if t = 3 then 0 else if t = 4 then 0 else t := by
  unfold rawF
  split_ifs <;> falso_omega

private theorem rawF_col3 (t : Nat) : rawF t 3 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 3
    else if t = 3 then 1 else 2 := by
  unfold rawF
  split_ifs <;> falso_omega

def famF (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotF m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawF y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawF at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawF a.val 1 = rawF b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    have h3 : rawF a.val 3 = rawF b.val 3 := congrArg Fin.val (h ⟨3, by omega⟩)
    rw [rawF_col1, rawF_col1] at h1
    rw [rawF_col3, rawF_col3] at h3
    apply Fin.ext
    split_ifs at h1 h3 <;> falso_omega

theorem famF_retract (m : Nat) :
    HasRetractPair (m + 5) (dotF m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have key : ∀ x : Fin (m + 5), x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotF m ⟨2, by omega⟩ (dotF m ⟨2, by omega⟩ x) = x := by
    intro x hx1 hx2
    have hx1' : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hx2' : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    rw [dotF_id m x hx1' hx2']
    exact dotF_id m x hx1' hx2'
  exact ⟨⟨2, by omega⟩, ⟨2, by omega⟩, key, key, rfl⟩

/-- Element 3 of family F is a classifier. -/
theorem famF_classifier (m : Nat) :
    ∀ x : Fin (m + 5),
      dotF m ⟨3, by omega⟩ x = ⟨0, by omega⟩ ∨
      dotF m ⟨3, by omega⟩ x = ⟨1, by omega⟩ := by
  intro x
  by_cases hx : x.val = 3
  · refine Or.inr (Fin.ext ?_)
    show rawF 3 x.val = 1
    unfold rawF
    split_ifs <;> falso_omega
  · refine Or.inl (Fin.ext ?_)
    show rawF 3 x.val = 0
    unfold rawF
    split_ifs <;> falso_omega

/-- Element 2 of family F is a pure non-classifier. -/
theorem famF_non_classifier (m : Nat) :
    ∀ x : Fin (m + 5), x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotF m ⟨2, by omega⟩ x ≠ ⟨0, by omega⟩ ∧
      dotF m ⟨2, by omega⟩ x ≠ ⟨1, by omega⟩ := by
  intro x hx1 hx2
  have hx1' : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
  have hx2' : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
  rw [dotF_id m x hx1' hx2']
  exact ⟨hx1, hx2⟩

/-- Family F violates the dichotomy at the mixed element 4:
    4·2 = 0 is absorber-valued while 4·3 = 2 is core-valued. -/
theorem famF_no_dichotomy (m : Nat) :
    ¬ HasDichotomy (m + 5) (dotF m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨-, hdich, -⟩
  rcases hdich ⟨4, by omega⟩ with h | h | h | h
  · exact fin_ne _ _ (by omega) h
  · exact fin_ne _ _ (by omega) h
  · -- classifier side fails at column 3: 4·3 = 2
    rcases h ⟨3, by omega⟩ with h' | h' | h' | h'
    · exact fin_ne _ _ (by omega) h'
    · exact fin_ne _ _ (by omega) h'
    · exact fin_ne (show 2 < m + 5 by omega) (show 0 < m + 5 by omega) (by omega) h'
    · exact fin_ne (show 2 < m + 5 by omega) (show 1 < m + 5 by omega) (by omega) h'
  · -- non-classifier side fails at column 2: 4·2 = 0
    rcases h ⟨2, by omega⟩ with h' | h' | h'
    · exact fin_ne _ _ (by omega) h'
    · exact fin_ne _ _ (by omega) h'
    · exact h'.1 rfl

/-- **S ⇏ D at every size n ≥ 5, non-vacuously**: R holds, a classifier
    and a pure non-classifier exist, and the dichotomy fails. -/
theorem s_without_d_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      (∃ cls : Fin n, cls ≠ M.zero₁ ∧ cls ≠ M.zero₂ ∧
        ∀ x : Fin n, M.dot cls x = M.zero₁ ∨ M.dot cls x = M.zero₂) ∧
      (∃ ncl : Fin n, ncl ≠ M.zero₁ ∧ ncl ≠ M.zero₂ ∧
        ∀ x : Fin n, x ≠ M.zero₁ → x ≠ M.zero₂ →
          M.dot ncl x ≠ M.zero₁ ∧ M.dot ncl x ≠ M.zero₂) ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famF m, famF_retract m,
    ⟨⟨3, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega), famF_classifier m⟩,
    ⟨⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega), famF_non_classifier m⟩,
    famF_no_dichotomy m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family Dm: H ∧ ¬R ∧ ¬D at every n ≥ 5
-- ═══════════════════════════════════════════════════════════════════

/-! Table (elements 0, 1 absorbers; column 1 is the identity column):
- row 2 (ICP b): `2·2 = 3`, `2·x = 4` for core x ≥ 3 — core-preserving,
  non-constant, non-injective;
- row 3 (ICP a): `3·2 = 2`, `3·x = 3` for core x ≥ 3;
- row 4 (ICP c): `4·4 = 3`, `4·x = 2` for other core x;
- rows y ≥ 5: constant 2 on core.

The factorization 3·x = 4·(2·x) holds on core, giving ICP. No element
acts injectively on the core (every row repeats a value on {2,3} or
{3,4}), so no retraction pair exists. No row is boolean on the core, so
no classifier exists and the dichotomy fails. -/

private def rawD (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if b = 0 then 0
  else if b = 1 then a
  else if a = 2 then (if b = 2 then 3 else 4)
  else if a = 3 then (if b = 2 then 2 else 3)
  else if a = 4 then (if b = 4 then 3 else 2)
  else 2

private theorem rawD_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawD a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawD
  split_ifs <;> falso_omega

def dotD (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawD a.val b.val, rawD_lt (by omega) a b⟩

/-- Column 1 of family Dm is the identity column. -/
private theorem rawD_col1 (t : Nat) : rawD t 1 = t := by
  unfold rawD
  split_ifs <;> falso_omega

def famD (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotD m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawD y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawD at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawD a.val 1 = rawD b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    rw [rawD_col1, rawD_col1] at h1
    exact Fin.ext h1

theorem famD_icp (m : Nat) :
    HasICP (m + 5) (dotD m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨3, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩,
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    ?_, ?_, ⟨⟨2, by omega⟩, ⟨3, by omega⟩,
      fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩⟩
  · -- Inert: 2 preserves the core (its core outputs are 3 and 4)
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
      · have h' : rawD 2 x.val = 0 := congrArg Fin.val h
        unfold rawD at h'
        split_ifs at h' <;> falso_omega
      · have h' : rawD 2 x.val = 1 := congrArg Fin.val h
        unfold rawD at h'
        split_ifs at h' <;> falso_omega
  · -- Compose: 3·x = 4·(2·x) on core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ?_)
      apply Fin.ext
      show rawD 3 x.val = rawD 4 (rawD 2 x.val)
      by_cases hx2 : x.val = 2
      · rw [hx2]; rfl
      · have h2x : rawD 2 x.val = 4 := by
          unfold rawD
          split_ifs <;> falso_omega
        rw [h2x]
        unfold rawD
        split_ifs <;> falso_omega
  · -- Non-triviality: 3·2 = 2 ≠ 3 = 3·3
    exact fin_ne (show 2 < m + 5 by omega) (show 3 < m + 5 by omega) (by omega)

theorem famD_no_retract (m : Nat) :
    ¬ HasRetractPair (m + 5) (dotD m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨s, r, hrs, -, -⟩
  by_cases hs4 : s.val = 4
  · -- s = 4 repeats on {2, 3}: 4·2 = 2 = 4·3
    have key : dotD m s ⟨2, by omega⟩ = dotD m s ⟨3, by omega⟩ := by
      apply Fin.ext
      show rawD s.val 2 = rawD s.val 3
      rw [hs4]; rfl
    have h2 := hrs ⟨2, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
    have h3 := hrs ⟨3, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
    refine fin_ne (show 2 < m + 5 by omega) (show 3 < m + 5 by omega) (by omega) ?_
    calc (⟨2, by omega⟩ : Fin (m + 5))
        = dotD m r (dotD m s ⟨2, by omega⟩) := h2.symm
      _ = dotD m r (dotD m s ⟨3, by omega⟩) := by rw [key]
      _ = ⟨3, by omega⟩ := h3
  · -- every other s repeats on {3, 4}: s·3 = s·4
    have key : dotD m s ⟨3, by omega⟩ = dotD m s ⟨4, by omega⟩ := by
      apply Fin.ext
      show rawD s.val 3 = rawD s.val 4
      unfold rawD
      split_ifs <;> falso_omega
    have h3 := hrs ⟨3, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
    have h4 := hrs ⟨4, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
    refine fin_ne (show 3 < m + 5 by omega) (show 4 < m + 5 by omega) (by omega) ?_
    calc (⟨3, by omega⟩ : Fin (m + 5))
        = dotD m r (dotD m s ⟨3, by omega⟩) := h3.symm
      _ = dotD m r (dotD m s ⟨4, by omega⟩) := by rw [key]
      _ = ⟨4, by omega⟩ := h4

theorem famD_no_dichotomy (m : Nat) :
    ¬ HasDichotomy (m + 5) (dotD m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨⟨cls, hcz1, hcz2, hbool⟩, -, -⟩
  have hcv0 : cls.val ≠ 0 := fun h => hcz1 (Fin.ext h)
  have hcv1 : cls.val ≠ 1 := fun h => hcz2 (Fin.ext h)
  rcases hbool ⟨2, by omega⟩ with h | h
  · have h' : rawD cls.val 2 = 0 := congrArg Fin.val h
    unfold rawD at h'
    split_ifs at h' <;> falso_omega
  · have h' : rawD cls.val 2 = 1 := congrArg Fin.val h
    unfold rawD at h'
    split_ifs at h' <;> falso_omega

/-- **C ⇏ S and C ⇏ D at every size n ≥ 5.** -/
theorem c_without_s_d_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasICP n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famD m, famD_icp m, famD_no_retract m, famD_no_dichotomy m⟩

-- ═══════════════════════════════════════════════════════════════════
-- The scaling theorem: all six non-implications at every size
-- ═══════════════════════════════════════════════════════════════════

/-- **The independence is not a small-size artifact** (scaling theorem).
    At every size n ≥ 5, all six pairwise non-implications among S, D,
    and C hold with witnesses of size exactly n (and D ⇏ S, D ⇏ H
    already from n ≥ 4 via `d_without_s_c_all_N`). -/
theorem independence_all_N (n : Nat) (hn : 5 ≤ n) :
    -- S ⇏ D and S ⇏ C
    (∃ M : Ext2PointedMagma n, HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- D ⇏ S and D ⇏ H
    (∃ M : Ext2PointedMagma n, HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- C ⇏ S and C ⇏ D
    (∃ M : Ext2PointedMagma n, HasICP n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧ ¬ HasDichotomy n M.dot M.zero₁ M.zero₂) := by
  refine ⟨?_, ?_, c_without_s_d_all_N n hn⟩
  · obtain ⟨M, h1, h2, h3⟩ := s_without_c_d_all_N n hn
    exact ⟨M, h1, h3, h2⟩
  · exact d_without_s_c_all_N n (by omega)

-- ═══════════════════════════════════════════════════════════════════
-- Family Hm: S ∧ D ∧ ¬C at every n ≥ 5
-- ═══════════════════════════════════════════════════════════════════

/-! Table: row 2 identity on core (sec = ret); row 3 a classifier
(`3·x = 1` iff `x = 3`); rows y ≥ 4 constant 2 on core with `y·1 = y`.
D holds with classifier 3 and non-classifiers {2} ∪ {y ≥ 4}. No ICP:
a composed element must be 2 or 3 (rows ≥ 4 are constant on core,
violating non-triviality), and each choice is refuted by evaluating the
factorization at columns 2 and 3. -/

private def rawHm (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then (if b = 0 then 0 else if b = 1 then 2 else b)
  else if a = 3 then (if b = 3 then 1 else 0)
  else if b = 0 then 0
  else if b = 1 then a
  else 2

private theorem rawHm_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawHm a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawHm
  split_ifs <;> falso_omega

def dotHm (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawHm a.val b.val, rawHm_lt (by omega) a b⟩

private theorem rawHm_col1 (t : Nat) : rawHm t 1 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
    else if t = 3 then 0 else t := by
  unfold rawHm
  split_ifs <;> falso_omega

private theorem rawHm_col3 (t : Nat) : rawHm t 3 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 3
    else if t = 3 then 1 else 2 := by
  unfold rawHm
  split_ifs <;> falso_omega

def famHm (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotHm m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawHm y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawHm at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawHm a.val 1 = rawHm b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    have h3 : rawHm a.val 3 = rawHm b.val 3 := congrArg Fin.val (h ⟨3, by omega⟩)
    rw [rawHm_col1, rawHm_col1] at h1
    rw [rawHm_col3, rawHm_col3] at h3
    apply Fin.ext
    split_ifs at h1 h3 <;> falso_omega

theorem famHm_retract (m : Nat) :
    HasRetractPair (m + 5) (dotHm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have hid : ∀ x : Fin (m + 5), x.val ≠ 0 → x.val ≠ 1 →
      dotHm m ⟨2, by omega⟩ x = x := by
    intro x hx0 hx1
    apply Fin.ext
    show rawHm 2 x.val = x.val
    unfold rawHm
    split_ifs <;> falso_omega
  have key : ∀ x : Fin (m + 5), x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotHm m ⟨2, by omega⟩ (dotHm m ⟨2, by omega⟩ x) = x := by
    intro x hx1 hx2
    have hx1' : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hx2' : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    rw [hid x hx1' hx2']
    exact hid x hx1' hx2'
  exact ⟨⟨2, by omega⟩, ⟨2, by omega⟩, key, key, rfl⟩

theorem famHm_dichotomy (m : Nat) :
    HasDichotomy (m + 5) (dotHm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨⟨3, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩, ?_, ?_⟩
  · -- element 3 is a classifier
    intro x
    by_cases hx : x.val = 3
    · exact Or.inr (Fin.ext (by show rawHm 3 x.val = 1; unfold rawHm; split_ifs <;> falso_omega))
    · exact Or.inl (Fin.ext (by show rawHm 3 x.val = 0; unfold rawHm; split_ifs <;> falso_omega))
  · -- the dichotomy
    intro y
    by_cases hy0 : y.val = 0
    · exact Or.inl (Fin.ext hy0)
    by_cases hy1 : y.val = 1
    · exact Or.inr (Or.inl (Fin.ext hy1))
    by_cases hy3 : y.val = 3
    · -- classifier side
      refine Or.inr (Or.inr (Or.inl fun x => ?_))
      refine Or.inr (Or.inr ?_)
      by_cases hx : x.val = 3
      · exact Or.inr (Fin.ext (by show rawHm y.val x.val = 1; unfold rawHm; split_ifs <;> falso_omega))
      · exact Or.inl (Fin.ext (by show rawHm y.val x.val = 0; unfold rawHm; split_ifs <;> falso_omega))
    · -- non-classifier side (y = 2 or y ≥ 4)
      refine Or.inr (Or.inr (Or.inr fun x => ?_))
      by_cases hx0 : x.val = 0
      · exact Or.inl (Fin.ext hx0)
      by_cases hx1 : x.val = 1
      · exact Or.inr (Or.inl (Fin.ext hx1))
      · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
        · have h' : rawHm y.val x.val = 0 := congrArg Fin.val h
          unfold rawHm at h'
          split_ifs at h' <;> falso_omega
        · have h' : rawHm y.val x.val = 1 := congrArg Fin.val h
          unfold rawHm at h'
          split_ifs at h' <;> falso_omega
  · -- non-degeneracy: 2·2 = 2
    refine ⟨⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      ⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fun h => fin_ne (show 2 < m + 5 by omega) (show 0 < m + 5 by omega) (by omega) h,
      fun h => fin_ne (show 2 < m + 5 by omega) (show 1 < m + 5 by omega) (by omega) h⟩

theorem famHm_no_icp (m : Nat) :
    ¬ HasICP (m + 5) (dotHm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
    hpres, hfact, x, y, hx1, hx2, hy1, hy2, hne⟩
  have hav0 : a.val ≠ 0 := fun h => ha1 (Fin.ext h)
  have hav1 : a.val ≠ 1 := fun h => ha2 (Fin.ext h)
  have hbv0 : b.val ≠ 0 := fun h => hb1 (Fin.ext h)
  have hbv1 : b.val ≠ 1 := fun h => hb2 (Fin.ext h)
  have hcv0 : c.val ≠ 0 := fun h => hc1 (Fin.ext h)
  have hcv1 : c.val ≠ 1 := fun h => hc2 (Fin.ext h)
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hacv : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbcv : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  -- a cannot be a constant-on-core row (y ≥ 4): non-triviality
  have hav : a.val = 2 ∨ a.val = 3 := by
    by_contra hav
    have haconst : ∀ t : Fin (m + 5), t.val ≠ 0 → t.val ≠ 1 →
        dotHm m a t = ⟨2, by omega⟩ := by
      intro t ht0 ht1
      apply Fin.ext
      show rawHm a.val t.val = 2
      unfold rawHm
      split_ifs <;> falso_omega
    have hxv0 : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hxv1 : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    have hyv0 : y.val ≠ 0 := fun h => hy1 (Fin.ext h)
    have hyv1 : y.val ≠ 1 := fun h => hy2 (Fin.ext h)
    rw [haconst x hxv0 hxv1, haconst y hyv0 hyv1] at hne
    exact hne rfl
  -- b = 3 fails core-preservation (3·2 = 0)
  by_cases hb3 : b.val = 3
  · rcases hpres ⟨2, by omega⟩ with h | h | h
    · exact fin_ne _ _ (by omega) h
    · exact fin_ne _ _ (by omega) h
    · exact h.1 (Fin.ext (by show rawHm b.val 2 = 0; unfold rawHm; split_ifs <;> falso_omega))
  by_cases hb2v : b.val = 2
  · -- b is the identity, so a ≠ b forces a = 3; evaluating at column 2
    -- pins c's column-2 value to 0, which no admissible c provides
    have ha3 : a.val = 3 := by omega
    have h2 : rawHm a.val 2 = rawHm c.val (rawHm b.val 2) :=
      congrArg Fin.val (((hfact ⟨2, by omega⟩).resolve_left
        (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega)))
    rw [ha3, hb2v] at h2
    have h2' : (0 : Nat) = rawHm c.val 2 := h2
    unfold rawHm at h2'
    split_ifs at h2' <;> falso_omega
  · -- b ≥ 4 is constant 2 on core: a's row is forced constant across columns 2, 3
    have hbc2 : rawHm b.val 2 = 2 := by
      unfold rawHm
      split_ifs <;> falso_omega
    have hbc3 : rawHm b.val 3 = 2 := by
      unfold rawHm
      split_ifs <;> falso_omega
    have h2 : rawHm a.val 2 = rawHm c.val (rawHm b.val 2) :=
      congrArg Fin.val (((hfact ⟨2, by omega⟩).resolve_left
        (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega)))
    have h3 : rawHm a.val 3 = rawHm c.val (rawHm b.val 3) :=
      congrArg Fin.val (((hfact ⟨3, by omega⟩).resolve_left
        (fin_ne _ _ (by omega))).resolve_left (fin_ne _ _ (by omega)))
    rw [hbc2] at h2
    rw [hbc3] at h3
    have hkey : rawHm a.val 2 = rawHm a.val 3 := h2.trans h3.symm
    rcases hav with ha2v | ha3v
    · rw [ha2v] at hkey
      have : (2 : Nat) = 3 := hkey
      omega
    · rw [ha3v] at hkey
      have : (0 : Nat) = 1 := hkey
      omega

/-- **S+D ⇏ C at every size n ≥ 5** (cube cell 2 at all sizes). -/
theorem sd_without_c_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famHm m, famHm_retract m, famHm_dichotomy m, famHm_no_icp m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family Cm: S ∧ C ∧ ¬D at every n ≥ 5
-- ═══════════════════════════════════════════════════════════════════

/-! Table: rows 2 and y ≥ 5 identity-like on core; rows 3 and 4 share the
core row `x = 2 ↦ 3, x ≥ 3 ↦ 2` (all core-valued) and differ on absorber
columns. ICP: (a, b, c) = (3, 2, 4) with b the identity. No classifier
exists (every row has the core-valued output at column 2), so ¬D.
This realizes cube cell 3 (S ∧ ¬D ∧ C) at every n ≥ 5 — previously
witnessed only at N=10 — and the bound is tight since C needs N ≥ 5. -/

private def rawCm (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 3 then (if b ≤ 1 then 0 else if b = 2 then 3 else 2)
  else if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else 2)
  else if b = 0 then 0
  else if b = 1 then a
  else b

private theorem rawCm_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawCm a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawCm
  split_ifs <;> falso_omega

def dotCm (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawCm a.val b.val, rawCm_lt (by omega) a b⟩

private theorem rawCm_col1 (t : Nat) : rawCm t 1 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 3 then 0
    else if t = 4 then 1 else t := by
  unfold rawCm
  split_ifs <;> falso_omega

private theorem rawCm_col2 (t : Nat) : rawCm t 2 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 3 then 3
    else if t = 4 then 3 else 2 := by
  unfold rawCm
  split_ifs <;> falso_omega

def famCm (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotCm m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawCm y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawCm at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawCm a.val 1 = rawCm b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    have h2 : rawCm a.val 2 = rawCm b.val 2 := congrArg Fin.val (h ⟨2, by omega⟩)
    rw [rawCm_col1, rawCm_col1] at h1
    rw [rawCm_col2, rawCm_col2] at h2
    apply Fin.ext
    split_ifs at h1 h2 <;> falso_omega

theorem famCm_retract (m : Nat) :
    HasRetractPair (m + 5) (dotCm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have hid : ∀ x : Fin (m + 5), x.val ≠ 0 → x.val ≠ 1 →
      dotCm m ⟨2, by omega⟩ x = x := by
    intro x hx0 hx1
    apply Fin.ext
    show rawCm 2 x.val = x.val
    unfold rawCm
    split_ifs <;> falso_omega
  have key : ∀ x : Fin (m + 5), x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotCm m ⟨2, by omega⟩ (dotCm m ⟨2, by omega⟩ x) = x := by
    intro x hx1 hx2
    have hx1' : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
    have hx2' : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
    rw [hid x hx1' hx2']
    exact hid x hx1' hx2'
  exact ⟨⟨2, by omega⟩, ⟨2, by omega⟩, key, key, rfl⟩

theorem famCm_icp (m : Nat) :
    HasICP (m + 5) (dotCm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨3, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩,
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    ?_, ?_, ⟨⟨2, by omega⟩, ⟨3, by omega⟩,
      fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩⟩
  · -- Inert: 2 is the identity on the core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
      · have h' : rawCm 2 x.val = 0 := congrArg Fin.val h
        unfold rawCm at h'
        split_ifs at h' <;> falso_omega
      · have h' : rawCm 2 x.val = 1 := congrArg Fin.val h
        unfold rawCm at h'
        split_ifs at h' <;> falso_omega
  · -- Compose: 3·x = 4·(2·x) on core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ?_)
      apply Fin.ext
      show rawCm 3 x.val = rawCm 4 (rawCm 2 x.val)
      have hin : rawCm 2 x.val = x.val := by
        unfold rawCm
        split_ifs <;> falso_omega
      rw [hin]
      unfold rawCm
      split_ifs <;> falso_omega
  · -- Non-triviality: 3·2 = 3 ≠ 2 = 3·3
    exact fin_ne (show 3 < m + 5 by omega) (show 2 < m + 5 by omega) (by omega)

theorem famCm_no_dichotomy (m : Nat) :
    ¬ HasDichotomy (m + 5) (dotCm m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨⟨cls, hcz1, hcz2, hbool⟩, -, -⟩
  have hcv0 : cls.val ≠ 0 := fun h => hcz1 (Fin.ext h)
  have hcv1 : cls.val ≠ 1 := fun h => hcz2 (Fin.ext h)
  rcases hbool ⟨2, by omega⟩ with h | h
  · have h' : rawCm cls.val 2 = 0 := congrArg Fin.val h
    unfold rawCm at h'
    split_ifs at h' <;> falso_omega
  · have h' : rawCm cls.val 2 = 1 := congrArg Fin.val h
    unfold rawCm at h'
    split_ifs at h' <;> falso_omega

/-- **S+C ⇏ D at every size n ≥ 5** (cube cell 3 at all sizes; tight,
    improving the single N=10 witness). -/
theorem sc_without_d_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasICP n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famCm m, famCm_retract m, famCm_icp m, famCm_no_dichotomy m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family B: D ∧ C ∧ ¬S at every n ≥ 5
-- ═══════════════════════════════════════════════════════════════════

/-! Table: row 2 (ICP b) maps core into {3, 2} non-injectively; rows 3
(ICP a) and 4 (ICP c) are boolean on core; rows y ≥ 5 constant 2 on
core. D holds (classifier 3), C holds via (3, 2, 4), and no element acts
injectively on the core (every row repeats on {3, 4}), so ¬S. -/

private def rawB (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then (if b = 0 then 0 else if b = 1 then 2 else if b = 2 then 3 else 2)
  else if a = 3 then (if b = 2 then 0 else if b ≤ 1 then 0 else 1)
  else if a = 4 then (if b = 2 then 1 else 0)
  else if b = 0 then 0
  else if b = 1 then a
  else 2

private theorem rawB_lt {n : Nat} (hn : 5 ≤ n) (a b : Fin n) :
    rawB a.val b.val < n := by
  have := a.isLt
  have := b.isLt
  unfold rawB
  split_ifs <;> falso_omega

def dotB (m : Nat) (a b : Fin (m + 5)) : Fin (m + 5) :=
  ⟨rawB a.val b.val, rawB_lt (by omega) a b⟩

private theorem rawB_col1 (t : Nat) : rawB t 1 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
    else if t = 3 then 0 else if t = 4 then 0 else t := by
  unfold rawB
  split_ifs <;> falso_omega

private theorem rawB_col2 (t : Nat) : rawB t 2 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 3
    else if t = 3 then 0 else if t = 4 then 1 else 2 := by
  unfold rawB
  split_ifs <;> falso_omega

private theorem rawB_col3 (t : Nat) : rawB t 3 =
    if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2
    else if t = 3 then 1 else if t = 4 then 0 else 2 := by
  unfold rawB
  split_ifs <;> falso_omega

def famB (m : Nat) : Ext2PointedMagma (m + 5) where
  dot := dotB m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawB y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawB at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawB a.val 1 = rawB b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    have h2 : rawB a.val 2 = rawB b.val 2 := congrArg Fin.val (h ⟨2, by omega⟩)
    have h3 : rawB a.val 3 = rawB b.val 3 := congrArg Fin.val (h ⟨3, by omega⟩)
    rw [rawB_col1, rawB_col1] at h1
    rw [rawB_col2, rawB_col2] at h2
    rw [rawB_col3, rawB_col3] at h3
    apply Fin.ext
    split_ifs at h1 h2 h3 <;> falso_omega

theorem famB_dichotomy (m : Nat) :
    HasDichotomy (m + 5) (dotB m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨⟨3, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩, ?_, ?_⟩
  · -- element 3 is a classifier
    intro x
    by_cases hx2 : x.val = 2
    · exact Or.inl (Fin.ext (by show rawB 3 x.val = 0; unfold rawB; split_ifs <;> falso_omega))
    by_cases hx01 : x.val ≤ 1
    · exact Or.inl (Fin.ext (by show rawB 3 x.val = 0; unfold rawB; split_ifs <;> falso_omega))
    · exact Or.inr (Fin.ext (by show rawB 3 x.val = 1; unfold rawB; split_ifs <;> falso_omega))
  · -- the dichotomy
    intro y
    by_cases hy0 : y.val = 0
    · exact Or.inl (Fin.ext hy0)
    by_cases hy1 : y.val = 1
    · exact Or.inr (Or.inl (Fin.ext hy1))
    by_cases hy3 : y.val = 3
    · -- classifier side, y = 3
      refine Or.inr (Or.inr (Or.inl fun x => ?_))
      refine Or.inr (Or.inr ?_)
      by_cases hx2 : x.val = 2
      · exact Or.inl (Fin.ext (by show rawB y.val x.val = 0; rw [hy3]; unfold rawB; split_ifs <;> falso_omega))
      by_cases hx01 : x.val ≤ 1
      · exact Or.inl (Fin.ext (by show rawB y.val x.val = 0; rw [hy3]; unfold rawB; split_ifs <;> falso_omega))
      · exact Or.inr (Fin.ext (by show rawB y.val x.val = 1; rw [hy3]; unfold rawB; split_ifs <;> falso_omega))
    by_cases hy4 : y.val = 4
    · -- classifier side, y = 4
      refine Or.inr (Or.inr (Or.inl fun x => ?_))
      refine Or.inr (Or.inr ?_)
      by_cases hx2 : x.val = 2
      · exact Or.inr (Fin.ext (by show rawB y.val x.val = 1; rw [hy4]; unfold rawB; split_ifs <;> falso_omega))
      · exact Or.inl (Fin.ext (by show rawB y.val x.val = 0; rw [hy4]; unfold rawB; split_ifs <;> falso_omega))
    · -- non-classifier side (y = 2 or y ≥ 5)
      refine Or.inr (Or.inr (Or.inr fun x => ?_))
      by_cases hx0 : x.val = 0
      · exact Or.inl (Fin.ext hx0)
      by_cases hx1 : x.val = 1
      · exact Or.inr (Or.inl (Fin.ext hx1))
      · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
        · have h' : rawB y.val x.val = 0 := congrArg Fin.val h
          unfold rawB at h'
          split_ifs at h' <;> falso_omega
        · have h' : rawB y.val x.val = 1 := congrArg Fin.val h
          unfold rawB at h'
          split_ifs at h' <;> falso_omega
  · -- non-degeneracy: 2·2 = 3
    refine ⟨⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      ⟨2, by omega⟩, fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fun h => fin_ne (show 3 < m + 5 by omega) (show 0 < m + 5 by omega) (by omega) h,
      fun h => fin_ne (show 3 < m + 5 by omega) (show 1 < m + 5 by omega) (by omega) h⟩

theorem famB_icp (m : Nat) :
    HasICP (m + 5) (dotB m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨3, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩,
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    fin_ne _ _ (by omega), fin_ne _ _ (by omega), fin_ne _ _ (by omega),
    ?_, ?_, ⟨⟨2, by omega⟩, ⟨3, by omega⟩,
      fin_ne _ _ (by omega), fin_ne _ _ (by omega),
      fin_ne _ _ (by omega), fin_ne _ _ (by omega), ?_⟩⟩
  · -- Inert: 2's core outputs are 3 (column 2) and 2 (columns ≥ 3)
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_⟩)
      · have h' : rawB 2 x.val = 0 := congrArg Fin.val h
        unfold rawB at h'
        split_ifs at h' <;> falso_omega
      · have h' : rawB 2 x.val = 1 := congrArg Fin.val h
        unfold rawB at h'
        split_ifs at h' <;> falso_omega
  · -- Compose: 3·x = 4·(2·x) on core
    intro x
    by_cases hx0 : x.val = 0
    · exact Or.inl (Fin.ext hx0)
    by_cases hx1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext hx1))
    · refine Or.inr (Or.inr ?_)
      apply Fin.ext
      show rawB 3 x.val = rawB 4 (rawB 2 x.val)
      by_cases hx2 : x.val = 2
      · rw [hx2]; rfl
      · have hin : rawB 2 x.val = 2 := by
          unfold rawB
          split_ifs <;> falso_omega
        rw [hin]
        unfold rawB
        split_ifs <;> falso_omega
  · -- Non-triviality: 3·2 = 0 ≠ 1 = 3·3
    exact fin_ne (show 0 < m + 5 by omega) (show 1 < m + 5 by omega) (by omega)

theorem famB_no_retract (m : Nat) :
    ¬ HasRetractPair (m + 5) (dotB m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨s, r, hrs, -, -⟩
  have key : dotB m s ⟨3, by omega⟩ = dotB m s ⟨4, by omega⟩ := by
    apply Fin.ext
    show rawB s.val 3 = rawB s.val 4
    unfold rawB
    split_ifs <;> falso_omega
  have h3 := hrs ⟨3, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  have h4 := hrs ⟨4, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  refine fin_ne (show 3 < m + 5 by omega) (show 4 < m + 5 by omega) (by omega) ?_
  calc (⟨3, by omega⟩ : Fin (m + 5))
      = dotB m r (dotB m s ⟨3, by omega⟩) := h3.symm
    _ = dotB m r (dotB m s ⟨4, by omega⟩) := by rw [key]
    _ = ⟨4, by omega⟩ := h4

/-- **D+C ⇏ S at every size n ≥ 5** (cube cell 5 at all sizes). -/
theorem dc_without_s_all_N (n : Nat) (hn : 5 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      HasICP n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  exact ⟨famB m, famB_dichotomy m, famB_icp m, famB_no_retract m⟩

-- ═══════════════════════════════════════════════════════════════════
-- Family Z: ¬S ∧ ¬D ∧ ¬C at every n ≥ 4
-- ═══════════════════════════════════════════════════════════════════

/-! The "no capability" family: every core row is `y·1 = y` (making
column 1 the identity column, hence extensionality) and 0 elsewhere.
Every core row is constant 0 on the core, so no element is injective on
core (¬S), no classifier exists — its column-1 output is itself (¬D) —
and every candidate composed element is constant on core (¬C). -/

private def rawZ (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a = 1 then 1
  else if b = 1 then a
  else 0

private theorem rawZ_lt {n : Nat} (hn : 4 ≤ n) (a b : Fin n) :
    rawZ a.val b.val < n := by
  have := a.isLt
  unfold rawZ
  split_ifs <;> falso_omega

def dotZ (m : Nat) (a b : Fin (m + 4)) : Fin (m + 4) :=
  ⟨rawZ a.val b.val, rawZ_lt (by omega) a b⟩

private theorem rawZ_col1 (t : Nat) : rawZ t 1 = t := by
  unfold rawZ
  split_ifs <;> falso_omega

def famZ (m : Nat) : Ext2PointedMagma (m + 4) where
  dot := dotZ m
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  zero₁_left := fun _ => rfl
  zero₂_left := fun _ => rfl
  zeros_distinct := fin_ne _ _ (by omega)
  no_other_zeros := by
    intro y h
    have h0 : rawZ y.val 0 = y.val := congrArg Fin.val (h ⟨0, by omega⟩)
    have : y.val = 0 ∨ y.val = 1 := by
      unfold rawZ at h0
      split_ifs at h0 <;> falso_omega
    rcases this with h' | h'
    · exact Or.inl (Fin.ext h')
    · exact Or.inr (Fin.ext h')
  extensional := by
    intro a b h
    have h1 : rawZ a.val 1 = rawZ b.val 1 := congrArg Fin.val (h ⟨1, by omega⟩)
    rw [rawZ_col1, rawZ_col1] at h1
    exact Fin.ext h1

theorem famZ_no_retract (m : Nat) :
    ¬ HasRetractPair (m + 4) (dotZ m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨s, r, hrs, -, -⟩
  have key : dotZ m s ⟨2, by omega⟩ = dotZ m s ⟨3, by omega⟩ := by
    apply Fin.ext
    show rawZ s.val 2 = rawZ s.val 3
    unfold rawZ
    split_ifs <;> falso_omega
  have h2 := hrs ⟨2, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  have h3 := hrs ⟨3, by omega⟩ (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))
  refine fin_ne (show 2 < m + 4 by omega) (show 3 < m + 4 by omega) (by omega) ?_
  calc (⟨2, by omega⟩ : Fin (m + 4))
      = dotZ m r (dotZ m s ⟨2, by omega⟩) := h2.symm
    _ = dotZ m r (dotZ m s ⟨3, by omega⟩) := by rw [key]
    _ = ⟨3, by omega⟩ := h3

theorem famZ_no_dichotomy (m : Nat) :
    ¬ HasDichotomy (m + 4) (dotZ m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨⟨cls, hcz1, hcz2, hbool⟩, -, -⟩
  have hcv0 : cls.val ≠ 0 := fun h => hcz1 (Fin.ext h)
  have hcv1 : cls.val ≠ 1 := fun h => hcz2 (Fin.ext h)
  rcases hbool ⟨1, by omega⟩ with h | h
  · have h' : rawZ cls.val 1 = 0 := congrArg Fin.val h
    rw [rawZ_col1] at h'
    exact hcv0 h'
  · have h' : rawZ cls.val 1 = 1 := congrArg Fin.val h
    rw [rawZ_col1] at h'
    exact hcv1 h'

theorem famZ_no_icp (m : Nat) :
    ¬ HasICP (m + 4) (dotZ m) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rintro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
    hpres, hfact, x, y, hx1, hx2, hy1, hy2, hne⟩
  have hav0 : a.val ≠ 0 := fun h => ha1 (Fin.ext h)
  have hav1 : a.val ≠ 1 := fun h => ha2 (Fin.ext h)
  have haconst : ∀ t : Fin (m + 4), t.val ≠ 0 → t.val ≠ 1 →
      dotZ m a t = ⟨0, by omega⟩ := by
    intro t ht0 ht1
    apply Fin.ext
    show rawZ a.val t.val = 0
    unfold rawZ
    split_ifs <;> falso_omega
  have hxv0 : x.val ≠ 0 := fun h => hx1 (Fin.ext h)
  have hxv1 : x.val ≠ 1 := fun h => hx2 (Fin.ext h)
  have hyv0 : y.val ≠ 0 := fun h => hy1 (Fin.ext h)
  have hyv1 : y.val ≠ 1 := fun h => hy2 (Fin.ext h)
  rw [haconst x hxv0 hxv1, haconst y hyv0 hyv1] at hne
  exact hne rfl

/-- **The empty profile at every size n ≥ 4** (cube cell 8 at all sizes). -/
theorem none_all_N (n : Nat) (hn : 4 ≤ n) :
    ∃ M : Ext2PointedMagma n,
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP n M.dot M.zero₁ M.zero₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact ⟨famZ m, famZ_no_retract m, famZ_no_dichotomy m, famZ_no_icp m⟩

-- ═══════════════════════════════════════════════════════════════════
-- The Boolean cube at every size
-- ═══════════════════════════════════════════════════════════════════

/-- Every `DichotomicRetractMagma` satisfies `HasDichotomy` (bridge from
    the bundled implication-form fields to the disjunction form). -/
theorem drm_hasDichotomy {n : Nat} (M : DichotomicRetractMagma n) :
    HasDichotomy n M.dot M.zero₁ M.zero₂ := by
  refine ⟨⟨M.cls, M.cls_ne_zero₁, M.cls_ne_zero₂, M.cls_boolean⟩, ?_, M.has_non_classifier⟩
  intro y
  by_cases hy1 : y = M.zero₁
  · exact Or.inl hy1
  by_cases hy2 : y = M.zero₂
  · exact Or.inr (Or.inl hy2)
  rcases M.dichotomy y hy1 hy2 with h | h
  · refine Or.inr (Or.inr (Or.inl fun x => ?_))
    by_cases hx1 : x = M.zero₁
    · exact Or.inl hx1
    by_cases hx2 : x = M.zero₂
    · exact Or.inr (Or.inl hx2)
    · exact Or.inr (Or.inr (h x hx1 hx2))
  · refine Or.inr (Or.inr (Or.inr fun x => ?_))
    by_cases hx1 : x = M.zero₁
    · exact Or.inl hx1
    by_cases hx2 : x = M.zero₂
    · exact Or.inr (Or.inl hx2)
    · exact Or.inr (Or.inr (h x hx1 hx2))

/-- **The Boolean cube at every size** (joint irredundance is not a
    small-size artifact). For every n ≥ 5, all eight Boolean profiles of
    (S, D, C) are realized by extensional 2-pointed magmas of size
    exactly n. Cell 1 is `WitnessAllN.lean`'s coexistence construction;
    the remaining seven cells are the parametric families of this file. -/
theorem boolean_cube_all_N (n : Nat) (hn : 5 ≤ n) :
    -- 1: S ∧ D ∧ C
    (∃ M : Ext2PointedMagma n, HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 2: S ∧ D ∧ ¬C
    (∃ M : Ext2PointedMagma n, HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 3: S ∧ ¬D ∧ C
    (∃ M : Ext2PointedMagma n, HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 4: S ∧ ¬D ∧ ¬C
    (∃ M : Ext2PointedMagma n, HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 5: ¬S ∧ D ∧ C
    (∃ M : Ext2PointedMagma n, ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 6: ¬S ∧ D ∧ ¬C
    (∃ M : Ext2PointedMagma n, ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 7: ¬S ∧ ¬D ∧ C
    (∃ M : Ext2PointedMagma n, ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ HasICP n M.dot M.zero₁ M.zero₂) ∧
    -- 8: ¬S ∧ ¬D ∧ ¬C
    (∃ M : Ext2PointedMagma n, ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧ ¬ HasICP n M.dot M.zero₁ M.zero₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cell 1: from the coexistence construction of WitnessAllN.lean
    obtain ⟨M, hicp⟩ := sdh_witness_all_N n hn
    exact ⟨M.toFaithfulRetractMagma.toE2PM, M.toFaithfulRetractMagma.hasRetractPair,
      drm_hasDichotomy M, hicp⟩
  · obtain ⟨M, h1, h2, h3⟩ := sd_without_c_all_N n hn
    exact ⟨M, h1, h2, h3⟩
  · obtain ⟨M, h1, h2, h3⟩ := sc_without_d_all_N n hn
    exact ⟨M, h1, h3, h2⟩
  · obtain ⟨M, h1, h2, h3⟩ := s_without_c_d_all_N n hn
    exact ⟨M, h1, h3, h2⟩
  · obtain ⟨M, h1, h2, h3⟩ := dc_without_s_all_N n hn
    exact ⟨M, h3, h1, h2⟩
  · obtain ⟨M, h1, h2, h3⟩ := d_without_s_c_all_N n (by omega)
    exact ⟨M, h2, h1, h3⟩
  · obtain ⟨M, h1, h2, h3⟩ := c_without_s_d_all_N n hn
    exact ⟨M, h2, h3, h1⟩
  · obtain ⟨M, h1, h2, h3⟩ := none_all_N n (by omega)
    exact ⟨M, h1, h2, h3⟩


end IndependenceAllN
end Dichotomic

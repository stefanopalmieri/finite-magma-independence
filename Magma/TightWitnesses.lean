import Magma.Dichotomic
import Magma.ICP
import Magma.E2PM

/-!
# Tight N=5 Counterexamples: S ⇏ D, S ⇏ C, and S+D ⇏ C

Three new minimum-size counterexamples, each improving a previously
larger witness, plus the pigeonhole lemma showing the S ⇏ D bound
is optimal.

## Results

- `s_not_implies_d_tight` (N=5): a `FaithfulRetractMagma` containing a
  classifier, a pure non-classifier, and a *mixed* element violating the
  dichotomy. Improves the N=8 `countermodel8`. Optimal: a non-vacuous
  dichotomy failure requires a classifier, a non-classifier, and a mixed
  element — three pairwise distinct core elements — so N ≥ 5
  (`no_nonvacuous_dichotomy_failure_at_4`).

- `s_not_implies_icp_structural_tight` (N=5): an E2PM whose three core
  elements act on the core as three distinct transpositions
  (L₂ = (3 4), L₃ = (2 3), L₄ = (2 4)). Every element is its own
  retraction pair (each Lᵧ is an involution), yet no ICP triple exists:
  the composition of two distinct transpositions is never a
  transposition. Improves the N=6 `sNoH6_e2pm`. Optimal: ICP is
  formulable only for N ≥ 5, so a structural (non-dimensional) failure
  cannot occur below N=5.

- `sd_not_implies_icp_tight` (N=5): an E2PM satisfying *both* R and D but
  not H. Improves the N=10 `dNotH` companion witness. With one classifier
  and two non-classifiers, ICP is impossible at N=5 for structural
  reasons (see `Forcing5.lean`), and this witness realizes that
  configuration. Also `d_not_implies_icp_structural_tight` (same bound,
  without R).
-/

set_option autoImplicit false

namespace Dichotomic

-- ═══════════════════════════════════════════════════════════════════
-- 1. S ⇏ D at N=5 (tight; improves countermodel8 at N=8)
-- ═══════════════════════════════════════════════════════════════════

/-! ```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 2, 2, 3, 4]   ← sec=ret (identity on core: pure non-classifier)
  3 [0, 0, 0, 1, 0]   ← classifier
  4 [0, 0, 0, 2, 2]   ← MIXED: 4·2 = 0 ∈ B but 4·3 = 2 ∉ B
```
All three dichotomy roles are inhabited (classifier 3, non-classifier 2,
mixed 4), so the dichotomy fails *non-vacuously*. -/

private def rawSnoD5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 2 | 2, 3 => 3 | 2, 4 => 4
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 0 | 4, 3 => 2 | 4, 4 => 2
  | _, _ => 0

private theorem rawSnoD5_bound (a b : Fin 5) : rawSnoD5 a.val b.val < 5 := by
  revert a b; decide

def dotSnoD5 (a b : Fin 5) : Fin 5 := ⟨rawSnoD5 a.val b.val, rawSnoD5_bound a b⟩

/-- The N=5 R⇏D witness is a full FaithfulRetractMagma (sec = ret = 2). -/
def sNoD5_frm : FaithfulRetractMagma 5 where
  dot := dotSnoD5
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

/-- Element 3 is a classifier: all outputs in {z₁, z₂}. -/
theorem sNoD5_has_classifier :
    ∀ x : Fin 5, dotSnoD5 3 x = 0 ∨ dotSnoD5 3 x = 1 := by decide

/-- Element 2 is a pure non-classifier: all core outputs outside {z₁, z₂}. -/
theorem sNoD5_has_non_classifier :
    ∀ x : Fin 5, x ≠ 0 → x ≠ 1 → dotSnoD5 2 x ≠ 0 ∧ dotSnoD5 2 x ≠ 1 := by decide

/-- Element 4 is mixed: 4·2 = 0 ∈ B but 4·3 = 2 ∉ B. -/
theorem sNoD5_element4_mixed :
    (dotSnoD5 4 2 = 0 ∨ dotSnoD5 4 2 = 1) ∧
    (dotSnoD5 4 3 ≠ 0 ∧ dotSnoD5 4 3 ≠ 1) := by decide

/-- The N=5 R⇏D witness violates the Kripke dichotomy. -/
theorem sNoD5_violates_dichotomy :
    ¬ (∀ y : Fin 5, y ≠ 0 → y ≠ 1 →
      (∀ x : Fin 5, x ≠ 0 → x ≠ 1 →
        dotSnoD5 y x = 0 ∨ dotSnoD5 y x = 1) ∨
      (∀ x : Fin 5, x ≠ 0 → x ≠ 1 →
        dotSnoD5 y x ≠ 0 ∧ dotSnoD5 y x ≠ 1)) := by decide

theorem sNoD5_has_retract : HasRetractPair 5 dotSnoD5 0 1 := by decide

theorem sNoD5_no_dichotomy : ¬ HasDichotomy 5 dotSnoD5 0 1 := by decide

/-- **S ⇏ D at N=5** (tight). A FaithfulRetractMagma with a classifier,
    a pure non-classifier, and a mixed element violating the dichotomy.
    The failure is non-vacuous: both dichotomy classes are inhabited and
    the failure is witnessed by a genuinely mixed element. Improves the
    N=8 countermodel; optimal by `no_nonvacuous_dichotomy_failure_at_4`. -/
theorem s_not_implies_d_tight :
    ∃ (_ : FaithfulRetractMagma 5),
    HasRetractPair 5 dotSnoD5 0 1 ∧ ¬ HasDichotomy 5 dotSnoD5 0 1 :=
  ⟨sNoD5_frm, sNoD5_has_retract, sNoD5_no_dichotomy⟩

-- ═══════════════════════════════════════════════════════════════════
-- 1a. Tightness: no non-vacuous dichotomy failure at N=4
-- ═══════════════════════════════════════════════════════════════════

/-- **Pigeonhole tightness for S ⇏ D**: no magma on 4 elements (with two
    distinct absorbers) can contain a classifier, a pure non-classifier,
    and a mixed element simultaneously. The three behavioral roles are
    pairwise distinct core elements, so together with the two absorbers
    they require |S| ≥ 5. This holds for *any* binary operation — no
    magma axioms are needed. -/
theorem no_nonvacuous_dichotomy_failure_at_4
    (dot : Fin 4 → Fin 4 → Fin 4) (z₁ z₂ : Fin 4) (hz : z₁ ≠ z₂)
    -- a classifier (boolean on core)
    (cls : Fin 4) (hc1 : cls ≠ z₁) (hc2 : cls ≠ z₂)
    (hcls : ∀ x : Fin 4, x ≠ z₁ → x ≠ z₂ → dot cls x = z₁ ∨ dot cls x = z₂)
    -- a pure non-classifier (non-boolean on core)
    (ncls : Fin 4) (hn1 : ncls ≠ z₁) (hn2 : ncls ≠ z₂)
    (hncls : ∀ x : Fin 4, x ≠ z₁ → x ≠ z₂ → dot ncls x ≠ z₁ ∧ dot ncls x ≠ z₂)
    -- a mixed element (both kinds of output on core)
    (mixd : Fin 4) (hm1 : mixd ≠ z₁) (hm2 : mixd ≠ z₂)
    (hmixb : ∃ x : Fin 4, x ≠ z₁ ∧ x ≠ z₂ ∧ (dot mixd x = z₁ ∨ dot mixd x = z₂))
    (hmixc : ∃ x : Fin 4, x ≠ z₁ ∧ x ≠ z₂ ∧ dot mixd x ≠ z₁ ∧ dot mixd x ≠ z₂) :
    False := by
  -- The three roles are pairwise distinct.
  have hcn : cls ≠ ncls := by
    intro h
    have hb := hcls cls hc1 hc2
    have hn := hncls cls hc1 hc2
    rw [← h] at hn
    rcases hb with h' | h'
    · exact hn.1 h'
    · exact hn.2 h'
  have hcm : cls ≠ mixd := by
    intro h
    obtain ⟨x, hx1, hx2, hxc⟩ := hmixc
    rcases hcls x hx1 hx2 with h' | h' <;> rw [h] at h'
    · exact hxc.1 h'
    · exact hxc.2 h'
  have hnm : ncls ≠ mixd := by
    intro h
    obtain ⟨x, hx1, hx2, hxb⟩ := hmixb
    have := hncls x hx1 hx2
    rw [h] at this
    rcases hxb with h' | h'
    · exact this.1 h'
    · exact this.2 h'
  -- Five pairwise distinct elements of Fin 4: impossible.
  have h1 : z₁.val ≠ z₂.val := fun h => hz (Fin.ext h)
  have h2 : cls.val ≠ z₁.val := fun h => hc1 (Fin.ext h)
  have h3 : cls.val ≠ z₂.val := fun h => hc2 (Fin.ext h)
  have h4 : ncls.val ≠ z₁.val := fun h => hn1 (Fin.ext h)
  have h5 : ncls.val ≠ z₂.val := fun h => hn2 (Fin.ext h)
  have h6 : mixd.val ≠ z₁.val := fun h => hm1 (Fin.ext h)
  have h7 : mixd.val ≠ z₂.val := fun h => hm2 (Fin.ext h)
  have h8 : cls.val ≠ ncls.val := fun h => hcn (Fin.ext h)
  have h9 : cls.val ≠ mixd.val := fun h => hcm (Fin.ext h)
  have h10 : ncls.val ≠ mixd.val := fun h => hnm (Fin.ext h)
  have b1 := z₁.isLt
  have b2 := z₂.isLt
  have b3 := cls.isLt
  have b4 := ncls.isLt
  have b5 := mixd.isLt
  omega

-- ═══════════════════════════════════════════════════════════════════
-- 2. S ⇏ C at N=5, structural (tight; improves sNoH6_e2pm at N=6)
-- ═══════════════════════════════════════════════════════════════════

/-! ```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 0, 2, 4, 3]   ← L₂ = transposition (3 4);  sec = ret = 2
  3 [0, 0, 3, 2, 4]   ← L₃ = transposition (2 3)
  4 [0, 0, 4, 3, 2]   ← L₄ = transposition (2 4)
```
The three core elements act on the core as three *distinct
transpositions*. Each is an involution, so every core element is its own
retraction pair (R holds three ways). But the composition of two distinct
transpositions moves three points — it is never a transposition — so no
factorization Lₐ = L꜀ ∘ L_b exists among distinct core elements: ICP
fails *structurally*, with the core exactly large enough (3 elements)
for ICP to be formulable. -/

private def rawSnoH5x : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 2 | 2, 3 => 4 | 2, 4 => 3
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 3 | 3, 3 => 2 | 3, 4 => 4
  | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 4 | 4, 3 => 3 | 4, 4 => 2
  | _, _ => 0

private theorem rawSnoH5x_bound (a b : Fin 5) : rawSnoH5x a.val b.val < 5 := by
  revert a b; decide

def dotSnoH5x (a b : Fin 5) : Fin 5 := ⟨rawSnoH5x a.val b.val, rawSnoH5x_bound a b⟩

/-- The N=5 structural R⇏H witness is a full FaithfulRetractMagma
    (sec = ret = 2, an involution on core). -/
def sNoH5_frm : FaithfulRetractMagma 5 where
  dot := dotSnoH5x
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

theorem sNoH5x_has_retract : HasRetractPair 5 dotSnoH5x 0 1 := by decide

/-- No ICP triple exists, despite the core having exactly the 3 elements
    ICP requires. -/
theorem sNoH5x_no_icp : ¬ HasICP 5 dotSnoH5x 0 1 := by decide

/-- **S ⇏ C at N=5, structural** (tight). A retraction pair does not
    imply ICP, at the minimum size where ICP is formulable at all.
    Improves the N=6 witness `s_not_implies_icp_structural`. -/
theorem s_not_implies_icp_structural_tight :
    ∃ (_ : FaithfulRetractMagma 5),
    HasRetractPair 5 dotSnoH5x 0 1 ∧ ¬ HasICP 5 dotSnoH5x 0 1 :=
  ⟨sNoH5_frm, sNoH5x_has_retract, sNoH5x_no_icp⟩

-- ═══════════════════════════════════════════════════════════════════
-- 3. D ⇏ C at N=5, structural — with and without R
--    (tight; improves the N=10 dNotH companion witness)
-- ═══════════════════════════════════════════════════════════════════

/-! Without R:
```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 1, 1, 1, 1]   ← classifier
  3 [0, 3, 2, 2, 2]   ← non-classifier (constant 2 on core)
  4 [0, 4, 2, 2, 2]   ← non-classifier (constant 2 on core)
```
With one classifier and two non-classifiers, any ICP triple must use all
three core elements, forcing an absorber-valued row to equal a
core-valued row — impossible (`Forcing5.lean` proves this configuration
constraint abstractly). -/

private def rawDnoH5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 1 | 2, 3 => 1 | 2, 4 => 1
  | 3, 0 => 0 | 3, 1 => 3 | 3, 2 => 2 | 3, 3 => 2 | 3, 4 => 2
  | 4, 0 => 0 | 4, 1 => 4 | 4, 2 => 2 | 4, 3 => 2 | 4, 4 => 2
  | _, _ => 0

private theorem rawDnoH5_bound (a b : Fin 5) : rawDnoH5 a.val b.val < 5 := by
  revert a b; decide

def dotDnoH5 (a b : Fin 5) : Fin 5 := ⟨rawDnoH5 a.val b.val, rawDnoH5_bound a b⟩

def dNoH5_e2pm : Ext2PointedMagma 5 where
  dot := dotDnoH5
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

theorem dNoH5_has_dichotomy : HasDichotomy 5 dotDnoH5 0 1 := by decide
theorem dNoH5_no_icp : ¬ HasICP 5 dotDnoH5 0 1 := by decide

/-- **D ⇏ C at N=5, structural** (tight). The dichotomy holds with 3
    core elements — exactly enough for ICP to be formulable — yet no
    ICP triple exists. Complements the vacuous tight bound at N=4
    (`kripke4_no_icp`) and improves the N=10 structural witness. -/
theorem d_not_implies_icp_structural_tight :
    ∃ (_ : Ext2PointedMagma 5),
    HasDichotomy 5 dotDnoH5 0 1 ∧ ¬ HasICP 5 dotDnoH5 0 1 :=
  ⟨dNoH5_e2pm, dNoH5_has_dichotomy, dNoH5_no_icp⟩

/-! With R (sec = ret = 2, identity on core):
```
     0  1  2  3  4
  0 [0, 0, 0, 0, 0]   ← z₁ (absorber)
  1 [1, 1, 1, 1, 1]   ← z₂ (absorber)
  2 [0, 2, 2, 3, 4]   ← sec=ret (identity on core, non-classifier)
  3 [0, 0, 0, 1, 0]   ← classifier
  4 [0, 4, 2, 2, 2]   ← non-classifier (constant 2 on core)
```
One classifier + two non-classifiers again: ICP is structurally
impossible, but now R and D both hold. -/

private def rawSDnoH5 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 2 | 2, 3 => 3 | 2, 4 => 4
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 4 | 4, 2 => 2 | 4, 3 => 2 | 4, 4 => 2
  | _, _ => 0

private theorem rawSDnoH5_bound (a b : Fin 5) : rawSDnoH5 a.val b.val < 5 := by
  revert a b; decide

def dotSDnoH5 (a b : Fin 5) : Fin 5 := ⟨rawSDnoH5 a.val b.val, rawSDnoH5_bound a b⟩

/-- The N=5 S+D+¬C witness is a full DichotomicRetractMagma. -/
def sdNoH5_drm : DichotomicRetractMagma 5 where
  dot := dotSDnoH5
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 2
  cls := 3
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

theorem sdNoH5_has_retract : HasRetractPair 5 dotSDnoH5 0 1 := by decide
theorem sdNoH5_has_dichotomy : HasDichotomy 5 dotSDnoH5 0 1 := by decide
theorem sdNoH5_no_icp : ¬ HasICP 5 dotSDnoH5 0 1 := by decide

/-- **S+D ⇏ C at N=5** (tight). Both R and D hold — as a full
    DichotomicRetractMagma — yet ICP fails structurally. Improves the
    N=10 companion witness `dNotH`; optimal since ICP needs N ≥ 5. -/
theorem sd_not_implies_icp_tight :
    ∃ (_ : DichotomicRetractMagma 5),
    HasRetractPair 5 dotSDnoH5 0 1 ∧ HasDichotomy 5 dotSDnoH5 0 1 ∧
    ¬ HasICP 5 dotSDnoH5 0 1 :=
  ⟨sdNoH5_drm, sdNoH5_has_retract, sdNoH5_has_dichotomy, sdNoH5_no_icp⟩

end Dichotomic

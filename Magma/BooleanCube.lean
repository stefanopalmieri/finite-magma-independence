import Magma.E2PM
import Magma.ICP
import Magma.Countermodels10
import Magma.Witness5

/-!
# The R × D × H Boolean Cube: Joint Irredundance

The pairwise-independence theorem shows no capability implies any other.
This file strengthens that result: every one of the 2³ = 8 Boolean
combinations of (R, D, H, ¬R, ¬D, ¬H) is inhabited by a finite
extensional 2-pointed magma.

Joint irredundance: if any cell of the cube were empty, some capability
would be determined by the other two as a Boolean function, collapsing
the triple to a pair. All eight cells are witnessed, so no such
reduction exists — R, D, and H carry independent information.

## Witness map

| Cell             | N  | Source                              |
|------------------|----|-------------------------------------|
| 1.  R ∧ D ∧ H    | 5  | `witness5_frm` + `w5_*`             |
| 2.  R ∧ D ∧ ¬H   | 4  | `kripke4` + `kripke4_no_icp`        |
| 3.  R ∧ ¬D ∧ H   | 10 | `hNotD` + ICP via Compose+Inert      |
| 4.  R ∧ ¬D ∧ ¬H  | 3  | `frm3` (new, this file)             |
| 5.  ¬R ∧ D ∧ H   | 5  | `cell5` (new, this file)            |
| 6.  ¬R ∧ D ∧ ¬H  | 4  | `dNoS4_e2pm` + vacuity at N=4       |
| 7.  ¬R ∧ ¬D ∧ H  | 5  | `hNoD5_e2pm` + `hNoD5_no_retract`    |
| 8.  ¬R ∧ ¬D ∧ ¬H | 3  | `cell8` (new, this file)            |

Cells 4, 5, and 8 require new witnesses (the first two are extremal in
different directions; cell 8 is the "no capability" magma). Cells 1–3
and 6–7 are covered by witnesses that already appear in the repository
under other names; this file adds the missing profile annotations and
assembles the umbrella theorem.

All verifications by `decide` (N ≤ 8) or `native_decide` (N = 10).
-/

set_option autoImplicit false

namespace KripkeWall

-- ═══════════════════════════════════════════════════════════════════
-- Cell 4: R ∧ ¬D ∧ ¬H at N=3
-- ═══════════════════════════════════════════════════════════════════

/-! Minimal R-only witness. Core = {2}, single element with a permutation row.
    R: `sec = ret = 2` satisfies `2·(2·x) = x` on the unique core element
    and `2·0 = 0` for anchoring.
    ¬D: only one core element, so a classifier *and* a non-classifier
    cannot coexist (D's non-degeneracy fails).
    ¬H: ICP needs 3 distinct core elements; core has 1. -/

private def rawFrm3 : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 2
  | _, _ => 0

private theorem rawFrm3_bound (a b : Fin 3) : rawFrm3 a.val b.val < 3 := by
  revert a b; decide

def dotFrm3 (a b : Fin 3) : Fin 3 := ⟨rawFrm3 a.val b.val, rawFrm3_bound a b⟩

def frm3_e2pm : Ext2PointedMagma 3 where
  dot := dotFrm3
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

theorem frm3_has_retract    : HasRetractPair 3 dotFrm3 0 1 := by decide
theorem frm3_no_dichotomy   : ¬ HasDichotomy  3 dotFrm3 0 1 := by decide
theorem frm3_no_icp         : ¬ HasICP         3 dotFrm3 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Cell 5: ¬R ∧ D ∧ H at N=5
-- ═══════════════════════════════════════════════════════════════════

/-! D+H without R. Core = {2,3,4}.
    ICP with (a,b,c) = (3,2,4): b=2 is core-preserving on core,
    and 3·x = 4·(2·x) for x ∈ core with 3 taking two distinct values.
    D: classifiers = {3,4} (rows ⊆ {0,1} on core), non-classifier = {2}.
    ¬R: for every candidate retraction index, the anchoring or the
    core identity fails. -/

private def rawCell5 : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 3 | 2, 3 => 4 | 2, 4 => 2
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 1 | 3, 3 => 0 | 3, 4 => 0
  | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 0 | 4, 3 => 1 | 4, 4 => 0
  | _, _ => 0

private theorem rawCell5_bound (a b : Fin 5) : rawCell5 a.val b.val < 5 := by
  revert a b; decide

def dotCell5 (a b : Fin 5) : Fin 5 := ⟨rawCell5 a.val b.val, rawCell5_bound a b⟩

def cell5_e2pm : Ext2PointedMagma 5 where
  dot := dotCell5
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

theorem cell5_no_retract    : ¬ HasRetractPair 5 dotCell5 0 1 := by decide
theorem cell5_has_dichotomy : HasDichotomy   5 dotCell5 0 1 := by decide
theorem cell5_has_icp       : HasICP          5 dotCell5 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Cell 8: ¬R ∧ ¬D ∧ ¬H at N=3
-- ═══════════════════════════════════════════════════════════════════

/-! The "no capability" witness. Core = {2} with a row that swaps the
    absorbers and fixes itself. No retraction pair exists because every
    ret candidate fails anchoring (ret·0 = 0): ret=0 trivially but then
    the core equation fails, ret=1 gives 1, ret=2 gives 1. -/

private def rawCell8 : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 2
  | _, _ => 0

private theorem rawCell8_bound (a b : Fin 3) : rawCell8 a.val b.val < 3 := by
  revert a b; decide

def dotCell8 (a b : Fin 3) : Fin 3 := ⟨rawCell8 a.val b.val, rawCell8_bound a b⟩

def cell8_e2pm : Ext2PointedMagma 3 where
  dot := dotCell8
  zero₁ := 0
  zero₂ := 1
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide

theorem cell8_no_retract   : ¬ HasRetractPair 3 dotCell8 0 1 := by decide
theorem cell8_no_dichotomy : ¬ HasDichotomy   3 dotCell8 0 1 := by decide
theorem cell8_no_icp       : ¬ HasICP         3 dotCell8 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- Profile annotations for existing witnesses used in the cube
-- ═══════════════════════════════════════════════════════════════════

/-- Kripke-4 is an FRM (so R holds) with D and ¬H. Used for cell 2. -/
theorem kripke4_has_retract   : HasRetractPair 4 dotK4 0 1 := by decide
theorem kripke4_has_dichotomy : HasDichotomy   4 dotK4 0 1 := by decide
theorem kripke4_no_icp_pred   : ¬ HasICP       4 dotK4 0 1 := by decide

/-- The N=10 H⇏D model has R (it is an FRM), ICP, and ¬D. Used for cell 3.
    `hNotD_has_icp` is already declared in `ICP.lean`; we add the two
    missing predicate forms here. -/
theorem hNotD_has_retract   : HasRetractPair 10 dotHnotD 0 1 := by native_decide
theorem hNotD_no_dichotomy_pred :
    ¬ HasDichotomy 10 dotHnotD 0 1 := by native_decide

/-- The tight N=4 D⇏R model has D, ¬R, and ¬H (vacuous). Used for cell 6. -/
theorem dNoS4_no_icp : ¬ HasICP 4 dotDnoS4 0 1 := by decide

/-- The tight N=5 H⇏D model has H, ¬D, and also ¬R. Used for cell 7. -/
theorem hNoD5_no_retract : ¬ HasRetractPair 5 dotHnoD5 0 1 := by decide

-- ═══════════════════════════════════════════════════════════════════
-- The eight cell theorems
-- ═══════════════════════════════════════════════════════════════════

/-- Cell 1: R ∧ D ∧ H is inhabited (N=5). -/
theorem cell_RDH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
      HasICP          n M.dot M.zero₁ M.zero₂ := by
  refine ⟨5, witness5_frm.toE2PM, ?_, ?_, ?_⟩
  · exact witness5_frm.hasRetractPair
  · decide
  · exact w5_has_icp

/-- Cell 2: R ∧ D ∧ ¬H is inhabited (N=4). -/
theorem cell_RD_noH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP        n M.dot M.zero₁ M.zero₂ :=
  ⟨4, kripke4.toFaithfulRetractMagma.toE2PM,
    kripke4_has_retract, kripke4_has_dichotomy, kripke4_no_icp_pred⟩

/-- Cell 3: R ∧ ¬D ∧ H is inhabited (N=10). -/
theorem cell_R_noD_H :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      HasRetractPair    n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy    n M.dot M.zero₁ M.zero₂ ∧
      HasICP             n M.dot M.zero₁ M.zero₂ :=
  ⟨10, hNotD.toE2PM,
    hNotD_has_retract, hNotD_no_dichotomy_pred, hNotD_has_icp⟩

/-- Cell 4: R ∧ ¬D ∧ ¬H is inhabited (N=3). -/
theorem cell_R_noD_noH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP        n M.dot M.zero₁ M.zero₂ :=
  ⟨3, frm3_e2pm, frm3_has_retract, frm3_no_dichotomy, frm3_no_icp⟩

/-- Cell 5: ¬R ∧ D ∧ H is inhabited (N=5). -/
theorem cell_noR_DH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy     n M.dot M.zero₁ M.zero₂ ∧
      HasICP            n M.dot M.zero₁ M.zero₂ :=
  ⟨5, cell5_e2pm, cell5_no_retract, cell5_has_dichotomy, cell5_has_icp⟩

/-- Cell 6: ¬R ∧ D ∧ ¬H is inhabited (N=4, H vacuous). -/
theorem cell_noR_D_noH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      HasDichotomy     n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP          n M.dot M.zero₁ M.zero₂ :=
  ⟨4, dNoS4_e2pm, dNoS4_no_retract, dNoS4_has_dichotomy, dNoS4_no_icp⟩

/-- Cell 7: ¬R ∧ ¬D ∧ H is inhabited (N=5). -/
theorem cell_noR_noD_H :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
      HasICP            n M.dot M.zero₁ M.zero₂ :=
  ⟨5, hNoD5_e2pm, hNoD5_no_retract, hNoD5_no_dichotomy, hNoD5_has_icp⟩

/-- Cell 8: ¬R ∧ ¬D ∧ ¬H is inhabited (N=3). -/
theorem cell_noR_noD_noH :
    ∃ (n : Nat) (M : Ext2PointedMagma n),
      ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
      ¬ HasICP          n M.dot M.zero₁ M.zero₂ :=
  ⟨3, cell8_e2pm, cell8_no_retract, cell8_no_dichotomy, cell8_no_icp⟩

-- ═══════════════════════════════════════════════════════════════════
-- Umbrella theorem: all 8 cells inhabited = joint irredundance
-- ═══════════════════════════════════════════════════════════════════

/-- **Joint irredundance of R, D, H.** Every Boolean combination of
    (R, D, H) is realized by a finite extensional 2-pointed magma.
    No predicate among R, D, H is expressible as a Boolean function
    of the other two: each cell of the 2³ cube is witnessed.

    This strengthens the pairwise-independence theorem
    (no capability implies any other) to: no capability is *determined*
    by the other two under any Boolean combination. -/
theorem boolean_cube_all_inhabited :
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
        HasICP          n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasICP        n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        HasRetractPair    n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasDichotomy    n M.dot M.zero₁ M.zero₂ ∧
        HasICP             n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasDichotomy n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasICP        n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        HasDichotomy     n M.dot M.zero₁ M.zero₂ ∧
        HasICP            n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        HasDichotomy     n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasICP          n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
        HasICP            n M.dot M.zero₁ M.zero₂) ∧
    (∃ (n : Nat) (M : Ext2PointedMagma n),
        ¬ HasRetractPair n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasDichotomy   n M.dot M.zero₁ M.zero₂ ∧
        ¬ HasICP          n M.dot M.zero₁ M.zero₂) :=
  ⟨cell_RDH, cell_RD_noH, cell_R_noD_H, cell_R_noD_noH,
   cell_noR_DH, cell_noR_D_noH, cell_noR_noD_H, cell_noR_noD_noH⟩

end KripkeWall

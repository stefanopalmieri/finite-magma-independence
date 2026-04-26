import Magma.Dichotomic
import Magma.ICP

/-!
# Parametric Coexistence Witness: R+D+ICP for All N ≥ 5

A construction giving, for every N ≥ 5, a `DichotomicRetractMagma N` whose
underlying operation also satisfies the Internal Composition Property (ICP).

This is the parametric scaling theorem (paper Theorem 7.3,
`thm:scaling-witness`): R+D+ICP coexistence persists at every cardinality
N ≥ 5.

## Construction (Cayley table T : Fin N → Fin N → Fin N)

```
  T(0, x) = 0                                   ← z₁ absorber
  T(1, x) = 1                                   ← z₂ absorber
  T(2, x) = x                                   ← sec = ret = identity
  T(3, x) = 1 if x ∈ {3, 4} else 0              ← classifier (yes-set {3,4})
  T(4, x) = 1 if x ∈ {1, 3, 4} else 0           ← classifier (yes-set {1,3,4})

  For k ∈ {5, ..., N-1}:
    T(k, 2) = k
    T(k, k) = 2
    T(k, x) = x  otherwise                      ← identity with cols 2,k swapped
```

## Witness assignments

  z₁ = 0    z₂ = 1    sec = ret = 2    cls = 3

## ICP triple

  (a, b, c) = (3, 2, 4): since b = 2 is identity on core, factorization
  reduces to T(3, x) = T(4, x) for x in core — the two classifiers agree
  everywhere except column 1 (which is an absorber column).

All proofs are universally quantified in N: `decide` does not apply.
-/

set_option autoImplicit false

namespace Dichotomic

-- ═══════════════════════════════════════════════════════════════════
-- The parametric construction
-- ═══════════════════════════════════════════════════════════════════

/-- The parametric Cayley operation on Fin N for any N ≥ 5. -/
def dotN (N : Nat) (h5 : 5 ≤ N) (a b : Fin N) : Fin N :=
  if a.val = 0 then ⟨0, by omega⟩
  else if a.val = 1 then ⟨1, by omega⟩
  else if a.val = 2 then b
  else if a.val = 3 then
    (if b.val = 3 ∨ b.val = 4 then ⟨1, by omega⟩ else ⟨0, by omega⟩)
  else if a.val = 4 then
    (if b.val = 1 ∨ b.val = 3 ∨ b.val = 4 then ⟨1, by omega⟩ else ⟨0, by omega⟩)
  else
    -- a.val ≥ 5: identity with columns 2 and a.val swapped
    if b.val = 2 then a
    else if b.val = a.val then ⟨2, by omega⟩
    else b

-- ═══════════════════════════════════════════════════════════════════
-- Helpful evaluation lemmas (one per row class), as `.val =` equations.
-- These avoid Fin-bound-proof headaches when used as rewrites in hypotheses.
-- ═══════════════════════════════════════════════════════════════════

section EvalLemmas
variable {N : Nat} (h5 : 5 ≤ N)

theorem dotN_row0_val (b : Fin N) : (dotN N h5 ⟨0, by omega⟩ b).val = 0 := by
  simp [dotN]

theorem dotN_row1_val (b : Fin N) : (dotN N h5 ⟨1, by omega⟩ b).val = 1 := by
  simp [dotN]

theorem dotN_row2_eq (b : Fin N) : dotN N h5 ⟨2, by omega⟩ b = b := by
  simp [dotN]

theorem dotN_row2_val (b : Fin N) : (dotN N h5 ⟨2, by omega⟩ b).val = b.val := by
  rw [dotN_row2_eq]

theorem dotN_row3_yes_val (b : Fin N) (hb : b.val = 3 ∨ b.val = 4) :
    (dotN N h5 ⟨3, by omega⟩ b).val = 1 := by
  simp [dotN, hb]

theorem dotN_row3_no_val (b : Fin N) (hb : b.val ≠ 3) (hb' : b.val ≠ 4) :
    (dotN N h5 ⟨3, by omega⟩ b).val = 0 := by
  simp [dotN, hb, hb']

theorem dotN_row4_yes_val (b : Fin N) (hb : b.val = 1 ∨ b.val = 3 ∨ b.val = 4) :
    (dotN N h5 ⟨4, by omega⟩ b).val = 1 := by
  simp [dotN, hb]

theorem dotN_row4_no_val (b : Fin N) (hb : b.val ≠ 1)
    (hb' : b.val ≠ 3) (hb'' : b.val ≠ 4) :
    (dotN N h5 ⟨4, by omega⟩ b).val = 0 := by
  simp [dotN, hb, hb', hb'']

theorem dotN_rowk_col2_val (a : Fin N) (ha : 5 ≤ a.val) :
    (dotN N h5 a ⟨2, by omega⟩).val = a.val := by
  unfold dotN
  have h0 : a.val ≠ 0 := by omega
  have h1 : a.val ≠ 1 := by omega
  have h2 : a.val ≠ 2 := by omega
  have h3 : a.val ≠ 3 := by omega
  have h4 : a.val ≠ 4 := by omega
  simp [h0, h1, h2, h3, h4]

theorem dotN_rowk_colk_val (a : Fin N) (ha : 5 ≤ a.val) :
    (dotN N h5 a a).val = 2 := by
  unfold dotN
  have h0 : a.val ≠ 0 := by omega
  have h1 : a.val ≠ 1 := by omega
  have h2 : a.val ≠ 2 := by omega
  have h3 : a.val ≠ 3 := by omega
  have h4 : a.val ≠ 4 := by omega
  simp [h0, h1, h2, h3, h4]

theorem dotN_rowk_other_val (a b : Fin N) (ha : 5 ≤ a.val)
    (hb2 : b.val ≠ 2) (hbk : b.val ≠ a.val) :
    (dotN N h5 a b).val = b.val := by
  unfold dotN
  have h0 : a.val ≠ 0 := by omega
  have h1 : a.val ≠ 1 := by omega
  have h2 : a.val ≠ 2 := by omega
  have h3 : a.val ≠ 3 := by omega
  have h4 : a.val ≠ 4 := by omega
  simp [h0, h1, h2, h3, h4, hb2, hbk]

end EvalLemmas

-- ═══════════════════════════════════════════════════════════════════
-- Axiom proofs
-- ═══════════════════════════════════════════════════════════════════

section AxiomProofs
variable {N : Nat} (h5 : 5 ≤ N)

theorem zero₁_left_dotN (x : Fin N) :
    dotN N h5 ⟨0, by omega⟩ x = ⟨0, by omega⟩ := by
  apply Fin.ext
  exact dotN_row0_val h5 x

theorem zero₂_left_dotN (x : Fin N) :
    dotN N h5 ⟨1, by omega⟩ x = ⟨1, by omega⟩ := by
  apply Fin.ext
  exact dotN_row1_val h5 x

theorem zeros_distinct_dotN : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
  intro h
  exact absurd (Fin.mk.inj_iff.mp h) (by omega)

theorem no_other_zeros_dotN (y : Fin N)
    (hy : ∀ x : Fin N, dotN N h5 y x = y) :
    y = ⟨0, by omega⟩ ∨ y = ⟨1, by omega⟩ := by
  match hyv : y.val, y.isLt with
  | 0, _ => left; exact Fin.ext hyv
  | 1, _ => right; exact Fin.ext hyv
  | 2, _ =>
    -- T(2, 0) = 0, but y = 2.
    exfalso
    have hy_eq : y = ⟨2, by omega⟩ := Fin.ext hyv
    have h := hy ⟨0, by omega⟩
    rw [hy_eq] at h
    have h0val : (⟨0, by omega⟩ : Fin N).val = 0 := rfl
    have h2val : (⟨2, by omega⟩ : Fin N).val = 2 := rfl
    have hval := congrArg Fin.val h
    rw [dotN_row2_val, h0val, h2val] at hval
    omega
  | 3, _ =>
    -- T(3, 3) = 1, but y = 3.
    exfalso
    have hy_eq : y = ⟨3, by omega⟩ := Fin.ext hyv
    have h := hy ⟨3, by omega⟩
    rw [hy_eq] at h
    have hval : (dotN N h5 ⟨3, by omega⟩ (⟨3, by omega⟩ : Fin N)).val =
                (⟨3, by omega⟩ : Fin N).val := congrArg Fin.val h
    rw [dotN_row3_yes_val h5 _ (Or.inl rfl)] at hval
    exact absurd hval (by omega)
  | 4, _ =>
    -- T(4, 3) = 1, but y = 4.
    exfalso
    have hy_eq : y = ⟨4, by omega⟩ := Fin.ext hyv
    have h := hy ⟨3, by omega⟩
    rw [hy_eq] at h
    have hval : (dotN N h5 ⟨4, by omega⟩ (⟨3, by omega⟩ : Fin N)).val =
                (⟨4, by omega⟩ : Fin N).val := congrArg Fin.val h
    rw [dotN_row4_yes_val h5 _ (Or.inr (Or.inl rfl))] at hval
    exact absurd hval (by omega)
  | k+5, hlt =>
    -- T(k+5, 0) = 0 (row is identity at col 0), but y = k+5.
    exfalso
    have hy_eq : y = ⟨k+5, hlt⟩ := Fin.ext hyv
    have h := hy ⟨0, by omega⟩
    rw [hy_eq] at h
    have hav5 : 5 ≤ (⟨k+5, hlt⟩ : Fin N).val := by show 5 ≤ k + 5; omega
    have hb_ne2 : (⟨0, by omega⟩ : Fin N).val ≠ 2 := by show (0 : Nat) ≠ 2; omega
    have hb_nek : (⟨0, by omega⟩ : Fin N).val ≠ (⟨k+5, hlt⟩ : Fin N).val := by
      show (0 : Nat) ≠ k + 5; omega
    have hval : (dotN N h5 ⟨k+5, hlt⟩ (⟨0, by omega⟩ : Fin N)).val =
                (⟨k+5, hlt⟩ : Fin N).val := congrArg Fin.val h
    rw [dotN_rowk_other_val h5 _ _ hav5 hb_ne2 hb_nek] at hval
    -- hval : 0 = k + 5
    exact absurd hval (by show (0 : Nat) ≠ k + 5; omega)

-- A small helper: distinguishing two rows by their values at a chosen input.
-- If two rows agree pointwise but their values differ at some specific input,
-- we have a contradiction. This packages the pattern.
private theorem rows_disagree_absurd {a b : Fin N} (x : Fin N) (n m : Nat)
    (hn : (dotN N h5 a x).val = n) (hm : (dotN N h5 b x).val = m) (hne : n ≠ m)
    (heq : ∀ x : Fin N, dotN N h5 a x = dotN N h5 b x) : False := by
  have h := heq x
  have hval : (dotN N h5 a x).val = (dotN N h5 b x).val := congrArg Fin.val h
  rw [hn, hm] at hval
  exact hne hval

theorem extensional_dotN (a b : Fin N)
    (h : ∀ x : Fin N, dotN N h5 a x = dotN N h5 b x) : a = b := by
  -- Case analysis on a.val and b.val. Same-row branches: equal. Different-row
  -- branches: invoke rows_disagree_absurd at a chosen distinguishing input.
  match hav : a.val, a.isLt, hbv : b.val, b.isLt with
  | 0, _, 0, _ => exact Fin.ext (hav.trans hbv.symm)
  | 0, _, 1, _ =>
    exfalso
    have ha : a = ⟨0, by omega⟩ := Fin.ext hav
    have hb : b = ⟨1, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row0_val h5 _)
        (by rw [hb]; exact dotN_row1_val h5 _)
        (by omega) h
  | 0, _, 2, _ =>
    exfalso
    have ha : a = ⟨0, by omega⟩ := Fin.ext hav
    have hb : b = ⟨2, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 0 2
        (by rw [ha]; exact dotN_row0_val h5 _)
        (by rw [hb]; exact dotN_row2_val h5 _)
        (by omega) h
  | 0, _, 3, _ =>
    exfalso
    have ha : a = ⟨0, by omega⟩ := Fin.ext hav
    have hb : b = ⟨3, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row0_val h5 _)
        (by rw [hb]; exact dotN_row3_yes_val h5 _ (Or.inl rfl))
        (by omega) h
  | 0, _, 4, _ =>
    exfalso
    have ha : a = ⟨0, by omega⟩ := Fin.ext hav
    have hb : b = ⟨4, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row0_val h5 _)
        (by rw [hb]; exact dotN_row4_yes_val h5 _ (Or.inr (Or.inl rfl)))
        (by omega) h
  | 0, _, j+5, hltb =>
    exfalso
    have ha : a = ⟨0, by omega⟩ := Fin.ext hav
    have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
    have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
    apply rows_disagree_absurd h5 (⟨j+5, hltb⟩ : Fin N) 0 2
        (by rw [ha]; exact dotN_row0_val h5 _)
        (by rw [hb]; exact dotN_rowk_colk_val h5 _ hb5)
        (by omega) h
  | 1, _, 0, _ =>
    exfalso
    have ha : a = ⟨1, by omega⟩ := Fin.ext hav
    have hb : b = ⟨0, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row1_val h5 _)
        (by rw [hb]; exact dotN_row0_val h5 _)
        (by omega) h
  | 1, _, 1, _ => exact Fin.ext (hav.trans hbv.symm)
  | 1, _, 2, _ =>
    exfalso
    have ha : a = ⟨1, by omega⟩ := Fin.ext hav
    have hb : b = ⟨2, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row1_val h5 _)
        (by rw [hb]; exact dotN_row2_val h5 _)
        (by omega) h
  | 1, _, 3, _ =>
    exfalso
    have ha : a = ⟨1, by omega⟩ := Fin.ext hav
    have hb : b = ⟨3, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row1_val h5 _)
        (by rw [hb]; exact dotN_row3_no_val h5 _ (by show (0 : Nat) ≠ 3; omega)
                                                  (by show (0 : Nat) ≠ 4; omega))
        (by omega) h
  | 1, _, 4, _ =>
    exfalso
    have ha : a = ⟨1, by omega⟩ := Fin.ext hav
    have hb : b = ⟨4, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row1_val h5 _)
        (by rw [hb]; exact dotN_row4_no_val h5 _ (by show (0 : Nat) ≠ 1; omega)
                                                 (by show (0 : Nat) ≠ 3; omega)
                                                 (by show (0 : Nat) ≠ 4; omega))
        (by omega) h
  | 1, _, j+5, hltb =>
    exfalso
    have ha : a = ⟨1, by omega⟩ := Fin.ext hav
    have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
    have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
    have hb_ne2 : (⟨0, by omega⟩ : Fin N).val ≠ 2 := by show (0 : Nat) ≠ 2; omega
    have hb_nek : (⟨0, by omega⟩ : Fin N).val ≠ (⟨j+5, hltb⟩ : Fin N).val := by
      show (0 : Nat) ≠ j + 5; omega
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row1_val h5 _)
        (by rw [hb]; exact dotN_rowk_other_val h5 _ _ hb5 hb_ne2 hb_nek)
        (by omega) h
  | 2, _, 0, _ =>
    exfalso
    have ha : a = ⟨2, by omega⟩ := Fin.ext hav
    have hb : b = ⟨0, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 2 0
        (by rw [ha]; exact dotN_row2_val h5 _)
        (by rw [hb]; exact dotN_row0_val h5 _)
        (by omega) h
  | 2, _, 1, _ =>
    exfalso
    have ha : a = ⟨2, by omega⟩ := Fin.ext hav
    have hb : b = ⟨1, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row2_val h5 _)
        (by rw [hb]; exact dotN_row1_val h5 _)
        (by omega) h
  | 2, _, 2, _ => exact Fin.ext (hav.trans hbv.symm)
  | 2, _, 3, _ =>
    exfalso
    have ha : a = ⟨2, by omega⟩ := Fin.ext hav
    have hb : b = ⟨3, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 2 0
        (by rw [ha]; exact dotN_row2_val h5 _)
        (by rw [hb]; exact dotN_row3_no_val h5 _ (by show (2 : Nat) ≠ 3; omega)
                                                  (by show (2 : Nat) ≠ 4; omega))
        (by omega) h
  | 2, _, 4, _ =>
    exfalso
    have ha : a = ⟨2, by omega⟩ := Fin.ext hav
    have hb : b = ⟨4, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 2 0
        (by rw [ha]; exact dotN_row2_val h5 _)
        (by rw [hb]; exact dotN_row4_no_val h5 _ (by show (2 : Nat) ≠ 1; omega)
                                                 (by show (2 : Nat) ≠ 3; omega)
                                                 (by show (2 : Nat) ≠ 4; omega))
        (by omega) h
  | 2, _, j+5, hltb =>
    exfalso
    have ha : a = ⟨2, by omega⟩ := Fin.ext hav
    have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
    have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 2 (j + 5)
        (by rw [ha]; exact dotN_row2_val h5 _)
        (by rw [hb]; exact dotN_rowk_col2_val h5 _ hb5)
        (by omega) h
  | 3, _, 0, _ =>
    exfalso
    have ha : a = ⟨3, by omega⟩ := Fin.ext hav
    have hb : b = ⟨0, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row3_yes_val h5 _ (Or.inl rfl))
        (by rw [hb]; exact dotN_row0_val h5 _)
        (by omega) h
  | 3, _, 1, _ =>
    exfalso
    have ha : a = ⟨3, by omega⟩ := Fin.ext hav
    have hb : b = ⟨1, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row3_no_val h5 _ (by show (0 : Nat) ≠ 3; omega)
                                                  (by show (0 : Nat) ≠ 4; omega))
        (by rw [hb]; exact dotN_row1_val h5 _)
        (by omega) h
  | 3, _, 2, _ =>
    exfalso
    have ha : a = ⟨3, by omega⟩ := Fin.ext hav
    have hb : b = ⟨2, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 0 2
        (by rw [ha]; exact dotN_row3_no_val h5 _ (by show (2 : Nat) ≠ 3; omega)
                                                  (by show (2 : Nat) ≠ 4; omega))
        (by rw [hb]; exact dotN_row2_val h5 _)
        (by omega) h
  | 3, _, 3, _ => exact Fin.ext (hav.trans hbv.symm)
  | 3, _, 4, _ =>
    exfalso
    have ha : a = ⟨3, by omega⟩ := Fin.ext hav
    have hb : b = ⟨4, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨1, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row3_no_val h5 _ (by show (1 : Nat) ≠ 3; omega)
                                                  (by show (1 : Nat) ≠ 4; omega))
        (by rw [hb]; exact dotN_row4_yes_val h5 _ (Or.inl rfl))
        (by omega) h
  | 3, _, j+5, hltb =>
    exfalso
    have ha : a = ⟨3, by omega⟩ := Fin.ext hav
    have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
    have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
    have hb_ne2 : (⟨3, by omega⟩ : Fin N).val ≠ 2 := by show (3 : Nat) ≠ 2; omega
    have hb_nek : (⟨3, by omega⟩ : Fin N).val ≠ (⟨j+5, hltb⟩ : Fin N).val := by
      show (3 : Nat) ≠ j + 5; omega
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 1 3
        (by rw [ha]; exact dotN_row3_yes_val h5 _ (Or.inl rfl))
        (by rw [hb]; exact dotN_rowk_other_val h5 _ _ hb5 hb_ne2 hb_nek)
        (by omega) h
  | 4, _, 0, _ =>
    exfalso
    have ha : a = ⟨4, by omega⟩ := Fin.ext hav
    have hb : b = ⟨0, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row4_yes_val h5 _ (Or.inr (Or.inl rfl)))
        (by rw [hb]; exact dotN_row0_val h5 _)
        (by omega) h
  | 4, _, 1, _ =>
    exfalso
    have ha : a = ⟨4, by omega⟩ := Fin.ext hav
    have hb : b = ⟨1, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_row4_no_val h5 _ (by show (0 : Nat) ≠ 1; omega)
                                                 (by show (0 : Nat) ≠ 3; omega)
                                                 (by show (0 : Nat) ≠ 4; omega))
        (by rw [hb]; exact dotN_row1_val h5 _)
        (by omega) h
  | 4, _, 2, _ =>
    exfalso
    have ha : a = ⟨4, by omega⟩ := Fin.ext hav
    have hb : b = ⟨2, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) 0 2
        (by rw [ha]; exact dotN_row4_no_val h5 _ (by show (2 : Nat) ≠ 1; omega)
                                                 (by show (2 : Nat) ≠ 3; omega)
                                                 (by show (2 : Nat) ≠ 4; omega))
        (by rw [hb]; exact dotN_row2_val h5 _)
        (by omega) h
  | 4, _, 3, _ =>
    exfalso
    have ha : a = ⟨4, by omega⟩ := Fin.ext hav
    have hb : b = ⟨3, by omega⟩ := Fin.ext hbv
    apply rows_disagree_absurd h5 (⟨1, by omega⟩ : Fin N) 1 0
        (by rw [ha]; exact dotN_row4_yes_val h5 _ (Or.inl rfl))
        (by rw [hb]; exact dotN_row3_no_val h5 _ (by show (1 : Nat) ≠ 3; omega)
                                                  (by show (1 : Nat) ≠ 4; omega))
        (by omega) h
  | 4, _, 4, _ => exact Fin.ext (hav.trans hbv.symm)
  | 4, _, j+5, hltb =>
    exfalso
    have ha : a = ⟨4, by omega⟩ := Fin.ext hav
    have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
    have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
    have hb_ne2 : (⟨3, by omega⟩ : Fin N).val ≠ 2 := by show (3 : Nat) ≠ 2; omega
    have hb_nek : (⟨3, by omega⟩ : Fin N).val ≠ (⟨j+5, hltb⟩ : Fin N).val := by
      show (3 : Nat) ≠ j + 5; omega
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 1 3
        (by rw [ha]; exact dotN_row4_yes_val h5 _ (Or.inr (Or.inl rfl)))
        (by rw [hb]; exact dotN_rowk_other_val h5 _ _ hb5 hb_ne2 hb_nek)
        (by omega) h
  | i+5, hlta, 0, _ =>
    exfalso
    have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
    have hb : b = ⟨0, by omega⟩ := Fin.ext hbv
    have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
    apply rows_disagree_absurd h5 (⟨i+5, hlta⟩ : Fin N) 2 0
        (by rw [ha]; exact dotN_rowk_colk_val h5 _ ha5)
        (by rw [hb]; exact dotN_row0_val h5 _)
        (by omega) h
  | i+5, hlta, 1, _ =>
    exfalso
    have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
    have hb : b = ⟨1, by omega⟩ := Fin.ext hbv
    have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
    have hb_ne2 : (⟨0, by omega⟩ : Fin N).val ≠ 2 := by show (0 : Nat) ≠ 2; omega
    have hb_nek : (⟨0, by omega⟩ : Fin N).val ≠ (⟨i+5, hlta⟩ : Fin N).val := by
      show (0 : Nat) ≠ i + 5; omega
    apply rows_disagree_absurd h5 (⟨0, by omega⟩ : Fin N) 0 1
        (by rw [ha]; exact dotN_rowk_other_val h5 _ _ ha5 hb_ne2 hb_nek)
        (by rw [hb]; exact dotN_row1_val h5 _)
        (by omega) h
  | i+5, hlta, 2, _ =>
    exfalso
    have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
    have hb : b = ⟨2, by omega⟩ := Fin.ext hbv
    have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
    apply rows_disagree_absurd h5 (⟨2, by omega⟩ : Fin N) (i + 5) 2
        (by rw [ha]; exact dotN_rowk_col2_val h5 _ ha5)
        (by rw [hb]; exact dotN_row2_val h5 _)
        (by omega) h
  | i+5, hlta, 3, _ =>
    exfalso
    have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
    have hb : b = ⟨3, by omega⟩ := Fin.ext hbv
    have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
    have hb_ne2 : (⟨3, by omega⟩ : Fin N).val ≠ 2 := by show (3 : Nat) ≠ 2; omega
    have hb_nek : (⟨3, by omega⟩ : Fin N).val ≠ (⟨i+5, hlta⟩ : Fin N).val := by
      show (3 : Nat) ≠ i + 5; omega
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 3 1
        (by rw [ha]; exact dotN_rowk_other_val h5 _ _ ha5 hb_ne2 hb_nek)
        (by rw [hb]; exact dotN_row3_yes_val h5 _ (Or.inl rfl))
        (by omega) h
  | i+5, hlta, 4, _ =>
    exfalso
    have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
    have hb : b = ⟨4, by omega⟩ := Fin.ext hbv
    have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
    have hb_ne2 : (⟨3, by omega⟩ : Fin N).val ≠ 2 := by show (3 : Nat) ≠ 2; omega
    have hb_nek : (⟨3, by omega⟩ : Fin N).val ≠ (⟨i+5, hlta⟩ : Fin N).val := by
      show (3 : Nat) ≠ i + 5; omega
    apply rows_disagree_absurd h5 (⟨3, by omega⟩ : Fin N) 3 1
        (by rw [ha]; exact dotN_rowk_other_val h5 _ _ ha5 hb_ne2 hb_nek)
        (by rw [hb]; exact dotN_row4_yes_val h5 _ (Or.inr (Or.inl rfl)))
        (by omega) h
  | i+5, hlta, j+5, hltb =>
    by_cases hij : i = j
    · exact Fin.ext (hav.trans (hij ▸ hbv.symm))
    · exfalso
      have ha : a = ⟨i+5, hlta⟩ := Fin.ext hav
      have hb : b = ⟨j+5, hltb⟩ := Fin.ext hbv
      have ha5 : 5 ≤ (⟨i+5, hlta⟩ : Fin N).val := by show 5 ≤ i + 5; omega
      have hb5 : 5 ≤ (⟨j+5, hltb⟩ : Fin N).val := by show 5 ≤ j + 5; omega
      -- Use x = a (= ⟨i+5, hlta⟩): T(a, a) = 2; T(b, a) = i+5 (since a ≠ 2 and a ≠ b).
      have hb_ne2 : (⟨i+5, hlta⟩ : Fin N).val ≠ 2 := by show i + 5 ≠ 2; omega
      have hb_nek : (⟨i+5, hlta⟩ : Fin N).val ≠ (⟨j+5, hltb⟩ : Fin N).val := by
        show i + 5 ≠ j + 5; omega
      apply rows_disagree_absurd h5 (⟨i+5, hlta⟩ : Fin N) 2 (i + 5)
          (by rw [ha]; exact dotN_rowk_colk_val h5 _ ha5)
          (by rw [hb]; exact dotN_rowk_other_val h5 _ _ hb5 hb_ne2 hb_nek)
          (by omega) h

theorem ret_sec_dotN (x : Fin N)
    (_hx1 : x ≠ ⟨0, by omega⟩) (_hx2 : x ≠ ⟨1, by omega⟩) :
    dotN N h5 ⟨2, by omega⟩ (dotN N h5 ⟨2, by omega⟩ x) = x := by
  rw [dotN_row2_eq, dotN_row2_eq]

theorem sec_ret_dotN (x : Fin N)
    (_hx1 : x ≠ ⟨0, by omega⟩) (_hx2 : x ≠ ⟨1, by omega⟩) :
    dotN N h5 ⟨2, by omega⟩ (dotN N h5 ⟨2, by omega⟩ x) = x := by
  rw [dotN_row2_eq, dotN_row2_eq]

theorem ret_zero₁_dotN :
    dotN N h5 ⟨2, by omega⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  rw [dotN_row2_eq]

theorem cls_boolean_dotN (x : Fin N) :
    dotN N h5 ⟨3, by omega⟩ x = ⟨0, by omega⟩ ∨
    dotN N h5 ⟨3, by omega⟩ x = ⟨1, by omega⟩ := by
  by_cases h3 : x.val = 3
  · right; apply Fin.ext; exact dotN_row3_yes_val h5 x (Or.inl h3)
  · by_cases h4 : x.val = 4
    · right; apply Fin.ext; exact dotN_row3_yes_val h5 x (Or.inr h4)
    · left; apply Fin.ext; exact dotN_row3_no_val h5 x h3 h4

theorem cls_ne_zero₁_dotN : (⟨3, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by
  intro h
  exact absurd (Fin.mk.inj_iff.mp h) (by omega)

theorem cls_ne_zero₂_dotN : (⟨3, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
  intro h
  exact absurd (Fin.mk.inj_iff.mp h) (by omega)

theorem dichotomy_dotN (y : Fin N)
    (hy1 : y ≠ ⟨0, by omega⟩) (hy2 : y ≠ ⟨1, by omega⟩) :
    (∀ x : Fin N, x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotN N h5 y x = ⟨0, by omega⟩ ∨ dotN N h5 y x = ⟨1, by omega⟩) ∨
    (∀ x : Fin N, x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, by omega⟩ →
      dotN N h5 y x ≠ ⟨0, by omega⟩ ∧ dotN N h5 y x ≠ ⟨1, by omega⟩) := by
  have hy1' : y.val ≠ 0 := fun h => hy1 (Fin.ext h)
  have hy2' : y.val ≠ 1 := fun h => hy2 (Fin.ext h)
  match hyv : y.val, y.isLt with
  | 0, _ => exact absurd hyv hy1'
  | 1, _ => exact absurd hyv hy2'
  | 2, _ =>
    -- y = 2 (identity): non-classifier on core.
    right
    intro x hx1 hx2
    have hy_eq : y = ⟨2, by omega⟩ := Fin.ext hyv
    rw [hy_eq, dotN_row2_eq]
    refine ⟨hx1, hx2⟩
  | 3, _ =>
    -- y = 3 (classifier): all-boolean.
    left
    intro x _ _
    have hy_eq : y = ⟨3, by omega⟩ := Fin.ext hyv
    rw [hy_eq]
    exact cls_boolean_dotN h5 x
  | 4, _ =>
    -- y = 4 (classifier): all-boolean.
    left
    intro x _ _
    have hy_eq : y = ⟨4, by omega⟩ := Fin.ext hyv
    rw [hy_eq]
    by_cases h1 : x.val = 1
    · right; apply Fin.ext; exact dotN_row4_yes_val h5 x (Or.inl h1)
    · by_cases h3 : x.val = 3
      · right; apply Fin.ext; exact dotN_row4_yes_val h5 x (Or.inr (Or.inl h3))
      · by_cases h4 : x.val = 4
        · right; apply Fin.ext; exact dotN_row4_yes_val h5 x (Or.inr (Or.inr h4))
        · left; apply Fin.ext; exact dotN_row4_no_val h5 x h1 h3 h4
  | k+5, hlt =>
    -- y = k+5: row is identity except cols 2 and k+5. All non-boolean on core.
    right
    intro x hx1 hx2
    have hy_eq : y = ⟨k+5, hlt⟩ := Fin.ext hyv
    have hy5 : 5 ≤ (⟨k+5, hlt⟩ : Fin N).val := by show 5 ≤ k + 5; omega
    rw [hy_eq]
    by_cases hb2 : x.val = 2
    · -- T(k+5, 2) = k+5. k+5 ≥ 5 ≠ 0, 1.
      have hxe : x = ⟨2, by omega⟩ := Fin.ext hb2
      rw [hxe]
      refine ⟨?_, ?_⟩
      · intro h
        have hval : (dotN N h5 ⟨k+5, hlt⟩ (⟨2, by omega⟩ : Fin N)).val =
                    (⟨0, by omega⟩ : Fin N).val := congrArg Fin.val h
        rw [dotN_rowk_col2_val h5 _ hy5] at hval
        exact absurd hval (by show k + 5 ≠ 0; omega)
      · intro h
        have hval : (dotN N h5 ⟨k+5, hlt⟩ (⟨2, by omega⟩ : Fin N)).val =
                    (⟨1, by omega⟩ : Fin N).val := congrArg Fin.val h
        rw [dotN_rowk_col2_val h5 _ hy5] at hval
        exact absurd hval (by show k + 5 ≠ 1; omega)
    · by_cases hbk : x.val = k + 5
      · -- T(k+5, k+5) = 2. 2 ≠ 0, 1.
        have hxe : x = ⟨k+5, hlt⟩ := Fin.ext hbk
        rw [hxe]
        have h0val : (⟨0, by omega⟩ : Fin N).val = 0 := rfl
        have h1val : (⟨1, by omega⟩ : Fin N).val = 1 := rfl
        refine ⟨?_, ?_⟩
        · intro h
          have hval := congrArg Fin.val h
          rw [dotN_rowk_colk_val h5 _ hy5, h0val] at hval
          omega
        · intro h
          have hval := congrArg Fin.val h
          rw [dotN_rowk_colk_val h5 _ hy5, h1val] at hval
          omega
      · -- T(k+5, x) = x. x ≠ 0, 1.
        have hxv_neK : x.val ≠ (⟨k+5, hlt⟩ : Fin N).val := by
          show x.val ≠ k + 5; exact hbk
        have ek := dotN_rowk_other_val h5 (⟨k+5, hlt⟩ : Fin N) x hy5 hb2 hxv_neK
        refine ⟨?_, ?_⟩
        · intro h
          have hval : (dotN N h5 ⟨k+5, hlt⟩ x).val =
                      (⟨0, by omega⟩ : Fin N).val := congrArg Fin.val h
          rw [ek] at hval
          exact hx1 (Fin.ext hval)
        · intro h
          have hval : (dotN N h5 ⟨k+5, hlt⟩ x).val =
                      (⟨1, by omega⟩ : Fin N).val := congrArg Fin.val h
          rw [ek] at hval
          exact hx2 (Fin.ext hval)

theorem has_non_classifier_dotN :
    ∃ y : Fin N, y ≠ ⟨0, by omega⟩ ∧ y ≠ ⟨1, by omega⟩ ∧
    ∃ x : Fin N, x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩ ∧
      dotN N h5 y x ≠ ⟨0, by omega⟩ ∧ dotN N h5 y x ≠ ⟨1, by omega⟩ := by
  refine ⟨⟨2, by omega⟩, ?_, ?_, ⟨2, by omega⟩, ?_, ?_, ?_, ?_⟩
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · rw [dotN_row2_eq]; intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · rw [dotN_row2_eq]; intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)

end AxiomProofs

-- ═══════════════════════════════════════════════════════════════════
-- Packaging into a DichotomicRetractMagma
-- ═══════════════════════════════════════════════════════════════════

/-- The parametric R+D witness as a `DichotomicRetractMagma N` for any N ≥ 5. -/
def witnessAllN_drm (N : Nat) (h5 : 5 ≤ N) : DichotomicRetractMagma N where
  dot := dotN N h5
  zero₁ := ⟨0, by omega⟩
  zero₂ := ⟨1, by omega⟩
  sec := ⟨2, by omega⟩
  ret := ⟨2, by omega⟩
  cls := ⟨3, by omega⟩
  zero₁_left := zero₁_left_dotN h5
  zero₂_left := zero₂_left_dotN h5
  zeros_distinct := zeros_distinct_dotN h5
  no_other_zeros := no_other_zeros_dotN h5
  extensional := extensional_dotN h5
  ret_sec := ret_sec_dotN h5
  sec_ret := sec_ret_dotN h5
  ret_zero₁ := ret_zero₁_dotN h5
  cls_boolean := cls_boolean_dotN h5
  cls_ne_zero₁ := cls_ne_zero₁_dotN h5
  cls_ne_zero₂ := cls_ne_zero₂_dotN h5
  dichotomy := dichotomy_dotN h5
  has_non_classifier := has_non_classifier_dotN h5

-- ═══════════════════════════════════════════════════════════════════
-- ICP for the parametric witness
-- ═══════════════════════════════════════════════════════════════════

/-- ICP holds for `dotN N h5` with witness triple (a, b, c) = (3, 2, 4):
    since b = 2 is the identity on core, the factorization
    `dot a x = dot c (dot b x)` reduces to `dot 3 x = dot 4 x` on core. -/
theorem witnessAllN_has_icp (N : Nat) (h5 : 5 ≤ N) :
    HasICP N (dotN N h5) ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  refine ⟨⟨3, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Pairwise distinct
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  -- Non-absorber
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
  -- b = 2 preserves core
  · intro x
    by_cases hx1 : x.val = 0
    · left; exact Fin.ext hx1
    · by_cases hx2 : x.val = 1
      · right; left; exact Fin.ext hx2
      · right; right
        rw [dotN_row2_eq]
        refine ⟨?_, ?_⟩
        · intro h; exact hx1 (congrArg Fin.val h)
        · intro h; exact hx2 (congrArg Fin.val h)
  -- Factorization: T(3, x) = T(4, T(2, x)) = T(4, x) on core
  · intro x
    by_cases hx1 : x.val = 0
    · left; exact Fin.ext hx1
    · by_cases hx2 : x.val = 1
      · right; left; exact Fin.ext hx2
      · right; right
        rw [dotN_row2_eq]
        apply Fin.ext
        by_cases h3 : x.val = 3
        · rw [dotN_row3_yes_val h5 x (Or.inl h3),
              dotN_row4_yes_val h5 x (Or.inr (Or.inl h3))]
        · by_cases h4 : x.val = 4
          · rw [dotN_row3_yes_val h5 x (Or.inr h4),
                dotN_row4_yes_val h5 x (Or.inr (Or.inr h4))]
          · rw [dotN_row3_no_val h5 x h3 h4,
                dotN_row4_no_val h5 x hx2 h3 h4]
  -- Non-triviality: T(3, 2) = 0, T(3, 3) = 1, distinct.
  · refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
    · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
    · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
    · intro h; exact absurd (Fin.mk.inj_iff.mp h) (by omega)
    · intro h
      have hval : (dotN N h5 ⟨3, by omega⟩ (⟨2, by omega⟩ : Fin N)).val =
                  (dotN N h5 ⟨3, by omega⟩ (⟨3, by omega⟩ : Fin N)).val :=
        congrArg Fin.val h
      rw [dotN_row3_no_val h5 _ (by show (2 : Nat) ≠ 3; omega)
                                  (by show (2 : Nat) ≠ 4; omega),
          dotN_row3_yes_val h5 _ (Or.inl rfl)] at hval
      exact absurd hval (by omega)

-- ═══════════════════════════════════════════════════════════════════
-- Combined existence theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **Parametric R+D+ICP coexistence at every N ≥ 5.** For every N ≥ 5,
    there exists a `DichotomicRetractMagma N` whose underlying operation
    satisfies the Internal Composition Property. -/
theorem sdh_witness_all_N (N : Nat) (h5 : 5 ≤ N) :
    ∃ (M : DichotomicRetractMagma N), HasICP N M.dot M.zero₁ M.zero₂ := by
  refine ⟨witnessAllN_drm N h5, ?_⟩
  unfold witnessAllN_drm
  exact witnessAllN_has_icp N h5

end Dichotomic

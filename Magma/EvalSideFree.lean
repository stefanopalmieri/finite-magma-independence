import Magma.ArtifactN8
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The Eval Side Is Free

The transfer principle behind two more law-set reductions: **on the
core, quote and eval are mutually inverse bijections, so laws about
quote transport to eval**. Consequences, both uniform in `n` and free
of any world assumption (no sorting, no swap — only the mutual
anchored retraction and core-valuedness):

* `eval_comm_of_quote_comm` — one of Stack A's four hygiene equations
  is redundant: if shift commutes with quote on the core, it commutes
  with eval. (Conjugate through the retraction:
  `r(γx) = r(γ(s(rx))) = r(s(γ(rx))) = γ(rx)`.)
* `eval_closure_of_quote_closure` — judge-closure under eval is free
  given judge-closure under quote. The proof is a finite-orbit
  argument: iterating the closure map yields a sequence of judges
  realizing `t∘sᵐ`; pigeonhole on `Fin n` repeats an element, so
  `t ≡ t∘s^d` for some `d ≥ 1`, and then `t∘r ≡ t∘s^{d-1}`, realized
  by the sequence's `(d-1)`-th judge.

Law-set consequence: Stack A's "shift commutes with eval" may be
deleted without changing the 228-model space
(`scripts/n8_enumerate_lexmin.py` re-verifies this empirically), and
an eval-side closure law would have been redundant to add. Together
with `StackAForced.lean`, the residue of choice in the law set is now:
quote-commutation, the involution, quote-side judge-closure, shift
distinctness, and the lex-min tie-break.
-/

set_option autoImplicit false

namespace Dichotomic

/-- **Hygiene's eval half is free.** If a core-valued operator γ
    commutes with the section on the core, it commutes with the
    retraction: conjugation through the mutual retraction. -/
theorem eval_comm_of_quote_comm (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (s r γ : Fin n)
    (hrN : NclSide n dot z₁ z₂ r) (hγN : NclSide n dot z₁ z₂ γ)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x)
    (hsr : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot s (dot r x) = x)
    (hcomm : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      dot γ (dot s x) = dot s (dot γ x)) :
    ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      dot γ (dot r x) = dot r (dot γ x) := by
  intro x hx1 hx2
  have hy : dot r x ≠ z₁ ∧ dot r x ≠ z₂ :=
    ((hrN x).resolve_left hx1).resolve_left hx2
  have hγy : dot γ (dot r x) ≠ z₁ ∧ dot γ (dot r x) ≠ z₂ :=
    ((hγN _).resolve_left hy.1).resolve_left hy.2
  calc dot γ (dot r x)
      = dot r (dot s (dot γ (dot r x))) := (hrs _ hγy.1 hγy.2).symm
    _ = dot r (dot γ (dot s (dot r x))) := by
        rw [← hcomm _ hy.1 hy.2]
    _ = dot r (dot γ x) := by rw [hsr x hx1 hx2]

-- ═══════════════════════════════════════════════════════════════════
-- Judge-closure transfers from quote to eval
-- ═══════════════════════════════════════════════════════════════════

/-- m-fold application of an element (outermost-last). -/
def actPow (n : Nat) (dot : Fin n → Fin n → Fin n) (s : Fin n) :
    Nat → Fin n → Fin n
  | 0, x => x
  | m + 1, x => dot s (actPow n dot s m x)

/-- m-fold application, innermost-first. -/
def actPow' (n : Nat) (dot : Fin n → Fin n → Fin n) (r : Fin n) :
    Nat → Fin n → Fin n
  | 0, x => x
  | m + 1, x => actPow' n dot r m (dot r x)

theorem actPow_core (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ s : Fin n) (hsN : NclSide n dot z₁ z₂ s) :
    ∀ (m : Nat) (x : Fin n), x ≠ z₁ → x ≠ z₂ →
      actPow n dot s m x ≠ z₁ ∧ actPow n dot s m x ≠ z₂ := by
  intro m
  induction m with
  | zero => exact fun x hx1 hx2 => ⟨hx1, hx2⟩
  | succ k ih =>
    intro x hx1 hx2
    obtain ⟨h1, h2⟩ := ih x hx1 hx2
    exact ((hsN _).resolve_left h1).resolve_left h2

theorem actPow'_core (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ r : Fin n) (hrN : NclSide n dot z₁ z₂ r) :
    ∀ (m : Nat) (x : Fin n), x ≠ z₁ → x ≠ z₂ →
      actPow' n dot r m x ≠ z₁ ∧ actPow' n dot r m x ≠ z₂ := by
  intro m
  induction m with
  | zero => exact fun x hx1 hx2 => ⟨hx1, hx2⟩
  | succ k ih =>
    intro x hx1 hx2
    obtain ⟨h1, h2⟩ := ((hrN x).resolve_left hx1).resolve_left hx2
    exact ih _ h1 h2

/-- Shift form: sᵐ⁺¹ = sᵐ ∘ s. -/
theorem actPow_shift (n : Nat) (dot : Fin n → Fin n → Fin n) (s : Fin n) :
    ∀ (m : Nat) (x : Fin n),
      actPow n dot s (m + 1) x = actPow n dot s m (dot s x) := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    show dot s (actPow n dot s (k + 1) x) = dot s (actPow n dot s k (dot s x))
    rw [ih x]

/-- Additivity: s^{a+b} = s^a ∘ s^b. -/
theorem actPow_add (n : Nat) (dot : Fin n → Fin n → Fin n) (s : Fin n) :
    ∀ (a b : Nat) (x : Fin n),
      actPow n dot s (a + b) x = actPow n dot s a (actPow n dot s b x) := by
  intro a b
  induction b with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [show a + (k + 1) = (a + k) + 1 from rfl, actPow_shift, ih,
      actPow_shift]

/-- The retraction inverts iterated sections on the core. -/
theorem actPow_actPow' (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ s r : Fin n) (hrN : NclSide n dot z₁ z₂ r)
    (hsr : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot s (dot r x) = x) :
    ∀ (m : Nat) (x : Fin n), x ≠ z₁ → x ≠ z₂ →
      actPow n dot s m (actPow' n dot r m x) = x := by
  intro m
  induction m with
  | zero => exact fun x _ _ => rfl
  | succ k ih =>
    intro x hx1 hx2
    obtain ⟨h1, h2⟩ := ((hrN x).resolve_left hx1).resolve_left hx2
    show dot s (actPow n dot s k (actPow' n dot r k (dot r x))) = x
    rw [ih _ h1 h2, hsr x hx1 hx2]

/-- The ordered-pair core of the finite-orbit argument, split out so
    both pigeonhole orderings can use it. -/
theorem eval_closure_step (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n) (s r : Fin n)
    (_hsN : NclSide n dot z₁ z₂ s) (hrN : NclSide n dot z₁ z₂ r)
    (hsr : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot s (dot r x) = x)
    (t : Fin n) (_ht1 : t ≠ z₁) (_ht2 : t ≠ z₂)
    (g : Nat → Fin n)
    (hgP : ∀ m, g m ≠ z₁ ∧ g m ≠ z₂ ∧ ClsSide n dot z₁ z₂ (g m))
    (hgA : ∀ m (x : Fin n), x ≠ z₁ → x ≠ z₂ →
      dot (g m) x = dot t (actPow n dot s m x))
    (i j : Nat) (hlt : i < j) (hgij : g i = g j) :
    ∃ t' : Fin n, (t' ≠ z₁ ∧ t' ≠ z₂ ∧ ClsSide n dot z₁ z₂ t') ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot t' x = dot t (dot r x) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = (d + 1) + i := ⟨j - i - 1, by omega⟩
  -- t ≡ t ∘ s^{d+1} on the core
  have hper : ∀ y : Fin n, y ≠ z₁ → y ≠ z₂ →
      dot t y = dot t (actPow n dot s (d + 1) y) := by
    intro y hy1 hy2
    have hry : actPow' n dot r i y ≠ z₁ ∧ actPow' n dot r i y ≠ z₂ :=
      actPow'_core n dot z₁ z₂ r hrN i y hy1 hy2
    have h1 := hgA i (actPow' n dot r i y) hry.1 hry.2
    have h2 := hgA ((d + 1) + i) (actPow' n dot r i y) hry.1 hry.2
    rw [hgij] at h1
    rw [h1] at h2
    rw [actPow_actPow' n dot z₁ z₂ s r hrN hsr i y hy1 hy2] at h2
    rw [actPow_add n dot s (d + 1) i] at h2
    rw [actPow_actPow' n dot z₁ z₂ s r hrN hsr i y hy1 hy2] at h2
    exact h2
  -- hence t ∘ r ≡ t ∘ s^d, realized by g d
  refine ⟨g d, hgP d, fun x hx1 hx2 => ?_⟩
  have hrx : dot r x ≠ z₁ ∧ dot r x ≠ z₂ :=
    ((hrN x).resolve_left hx1).resolve_left hx2
  rw [hgA d x hx1 hx2, hper (dot r x) hrx.1 hrx.2, actPow_shift,
    hsr x hx1 hx2]


/-- **Judge-closure under eval is free given judge-closure under
    quote.** Finite-orbit argument: the closure sequence realizes
    `t∘sᵐ` for every m; two of its members coincide by pigeonhole, so
    `t ≡ t∘s^d` on the core with `d ≥ 1`, whence `t∘r ≡ t∘s^{d-1}`,
    realized by the sequence. No world assumptions: only the mutual
    retraction and core-valuedness. -/
theorem eval_closure_of_quote_closure (n : Nat)
    (dot : Fin n → Fin n → Fin n) (z₁ z₂ : Fin n)
    (s r : Fin n)
    (hsN : NclSide n dot z₁ z₂ s) (hrN : NclSide n dot z₁ z₂ r)
    (hsr : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot s (dot r x) = x)
    (hclo : ∀ t : Fin n, t ≠ z₁ → t ≠ z₂ → ClsSide n dot z₁ z₂ t →
      ∃ t' : Fin n, (t' ≠ z₁ ∧ t' ≠ z₂ ∧ ClsSide n dot z₁ z₂ t') ∧
        ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot t' x = dot t (dot s x)) :
    ∀ t : Fin n, t ≠ z₁ → t ≠ z₂ → ClsSide n dot z₁ z₂ t →
      ∃ t' : Fin n, (t' ≠ z₁ ∧ t' ≠ z₂ ∧ ClsSide n dot z₁ z₂ t') ∧
        ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot t' x = dot t (dot r x) := by
  intro t ht1 ht2 htC
  -- the closure sequence: a judge realizing t∘sᵐ for every m
  have hseq : ∀ m : Nat, ∃ u : Fin n,
      (u ≠ z₁ ∧ u ≠ z₂ ∧ ClsSide n dot z₁ z₂ u) ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
        dot u x = dot t (actPow n dot s m x) := by
    intro m
    induction m with
    | zero => exact ⟨t, ⟨ht1, ht2, htC⟩, fun x _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨u, hu, hact⟩ := ih
      obtain ⟨u', hu', hact'⟩ := hclo u hu.1 hu.2.1 hu.2.2
      refine ⟨u', hu', fun x hx1 hx2 => ?_⟩
      have hsx : dot s x ≠ z₁ ∧ dot s x ≠ z₂ :=
        ((hsN x).resolve_left hx1).resolve_left hx2
      rw [hact' x hx1 hx2, hact _ hsx.1 hsx.2, ← actPow_shift]
  choose g hgP hgA using hseq
  -- pigeonhole: two indices among n+1 share an element
  obtain ⟨i, j, hij, hgij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => g i.val)
      (by simp only [Fintype.card_fin]; omega)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact eval_closure_step n dot z₁ z₂ s r hsN hrN hsr t ht1 ht2
      g hgP hgA i.val j.val hlt hgij
  · exact eval_closure_step n dot z₁ z₂ s r hsN hrN hsr t ht1 ht2
      g hgP hgA j.val i.val hlt hgij.symm

end Dichotomic

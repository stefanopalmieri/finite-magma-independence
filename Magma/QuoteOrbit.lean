import Magma.EvalSideFree
import Mathlib.Data.Fintype.BigOperators

/-!
# The Quote-Side Residue, Reduced

Three more reductions of Stack A's remaining choices, built on the
iterate machinery of `EvalSideFree.lean`:

* `faithful_finite_order` — **reversibility is free**: every faithful
  core-valued operator has finite order on the core (pigeonhole over
  the finite function space). A hygienic renaming operator is
  automatically undoable — by iterating itself. Instantiated for
  quotation itself (`quote_finite_order`): iterated quotation always
  cycles.
* `swap_even_order` — **the order is even**: in the class-swapping
  world an operator's odd powers swap the classifier blocks, so no
  odd power can be the identity. Together with the previous theorem,
  shift's order is a finite even number; Stack A's involution law is
  exactly the choice of the *minimum*, 2 — a tie-break in the same
  family as lex-min, no longer an axiom of substance.
* `orbit_quote_closure` / `orbit_eval_closure` — **judge-closure
  reduces to orbit-realization**: if quotation has core order d and
  the d actions κ∘sᵐ are realized by judges, that family is closed
  under precomposition with quote *and* with eval — modular
  arithmetic on the orbit. The residual content of Stack A's
  judge-closure law is therefore only about judges *outside* the
  introspector's orbit (at N = 8 with involutive quote: the one free
  judge, which the lex-min table resolves into `shift?`).

Ledger after this file. Derived: the world, the size, the eval side,
reversibility, evenness of shift's order, closure of the realized
orbit. Chosen: quote-commutation (the *definition* of hygienic),
order = minimum (tie-break), orbit-realization plus closure for
non-orbit judges, shift's action-distinctness, lex-min (tie-break).
-/

set_option autoImplicit false

namespace Dichotomic

/-- Iterates of a faithful operator are injective on the core. -/
theorem actPow_inj (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ γ : Fin n) (hγN : NclSide n dot z₁ z₂ γ)
    (hfaith : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot γ x = dot γ y → x = y) :
    ∀ (m : Nat) (x y : Fin n), x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      actPow n dot γ m x = actPow n dot γ m y → x = y := by
  intro m
  induction m with
  | zero => exact fun x y _ _ _ _ h => h
  | succ k ih =>
    intro x y hx1 hx2 hy1 hy2 h
    have hx := actPow_core n dot z₁ z₂ γ hγN k x hx1 hx2
    have hy := actPow_core n dot z₁ z₂ γ hγN k y hy1 hy2
    exact ih x y hx1 hx2 hy1 hy2 (hfaith _ _ hx.1 hx.2 hy.1 hy.2 h)

/-- Ordered-pair core of the finite-order argument. -/
theorem finite_order_step (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ γ : Fin n) (hγN : NclSide n dot z₁ z₂ γ)
    (hfaith : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot γ x = dot γ y → x = y)
    (i j : Nat) (hlt : i < j)
    (hf : (fun x : Fin n => actPow n dot γ i x) =
          (fun x : Fin n => actPow n dot γ j x)) :
    ∃ d : Nat, 1 ≤ d ∧ ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      actPow n dot γ d x = x := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  refine ⟨d + 1, by omega, fun x hx1 hx2 => ?_⟩
  have hdx := actPow_core n dot z₁ z₂ γ hγN (d + 1) x hx1 hx2
  have h := congrFun hf x
  rw [actPow_add n dot γ i (d + 1)] at h
  exact (actPow_inj n dot z₁ z₂ γ hγN hfaith i _ x hdx.1 hdx.2 hx1 hx2
    h.symm)

/-- **Reversibility is free**: every faithful core-valued operator has
    finite order on the core — pigeonhole over the finite function
    space repeats two iterates, and injectivity cancels the common
    prefix. -/
theorem faithful_finite_order (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ γ : Fin n) (hγN : NclSide n dot z₁ z₂ γ)
    (hfaith : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot γ x = dot γ y → x = y) :
    ∃ d : Nat, 1 ≤ d ∧ ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      actPow n dot γ d x = x := by
  obtain ⟨i, j, hij, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun m : Fin (n ^ n + 1) => (fun x : Fin n => actPow n dot γ m.val x))
      (by simp only [Fintype.card_fun, Fintype.card_fin]; omega)
  have hvij : i.val ≠ j.val := fun h => hij (Fin.val_injective h)
  rcases lt_or_gt_of_ne hvij with hlt | hlt
  · exact finite_order_step n dot z₁ z₂ γ hγN hfaith i.val j.val hlt hf
  · exact finite_order_step n dot z₁ z₂ γ hγN hfaith j.val i.val hlt hf.symm

/-- Quotation itself always cycles: the retraction makes the section
    faithful, so iterated quotation has finite core order. -/
theorem quote_finite_order (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ s r : Fin n) (hsN : NclSide n dot z₁ z₂ s)
    (hrs : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot r (dot s x) = x) :
    ∃ d : Nat, 1 ≤ d ∧ ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      actPow n dot s d x = x := by
  refine faithful_finite_order n dot z₁ z₂ s hsN ?_
  intro x y hx1 hx2 hy1 hy2 h
  have h1 := hrs x hx1 hx2
  rw [h, hrs y hy1 hy2] at h1
  exact h1.symm

/-- **The order is even**: in the class-swapping world, odd powers of
    an operator swap the classifier blocks, so no odd power fixes a
    classifier — the identity is even. -/
theorem swap_even_order (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n)
    (hswap : ClassSwapping n dot z₁ z₂)
    (γ : Fin n) (hγ1 : γ ≠ z₁) (hγ2 : γ ≠ z₂) (hγN : NclSide n dot z₁ z₂ γ)
    (τ : Fin n) (hτ1 : τ ≠ z₁) (hτ2 : τ ≠ z₂) (hτC : ClsSide n dot z₁ z₂ τ)
    (d : Nat) (_hd : 1 ≤ d)
    (hord : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → actPow n dot γ d x = x) :
    d % 2 = 0 := by
  -- parity invariant: even iterates keep τ a classifier, odd make it
  -- a non-classifier
  have hside : ∀ m : Nat,
      (m % 2 = 0 → ClsSide n dot z₁ z₂ (actPow n dot γ m τ)) ∧
      (m % 2 = 1 → NclSide n dot z₁ z₂ (actPow n dot γ m τ)) := by
    intro m
    induction m with
    | zero => exact ⟨fun _ => hτC, fun h => absurd h (by omega)⟩
    | succ k ih =>
      have hk := actPow_core n dot z₁ z₂ γ hγN k τ hτ1 hτ2
      constructor
      · intro h
        have hk1 : k % 2 = 1 := by omega
        exact (hswap γ _ hγ1 hγ2 hk.1 hk.2 hγN).2 (ih.2 hk1)
      · intro h
        have hk0 : k % 2 = 0 := by omega
        exact (hswap γ _ hγ1 hγ2 hk.1 hk.2 hγN).1 (ih.1 hk0)
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · exact h
  · exfalso
    -- an odd identity would make τ both a classifier and not
    have hN : NclSide n dot z₁ z₂ (actPow n dot γ d τ) := (hside d).2 h
    rw [hord τ hτ1 hτ2] at hN
    rcases (hτC τ).resolve_left hτ1 |>.resolve_left hτ2 with hz | hz
    · exact ((hN τ).resolve_left hτ1 |>.resolve_left hτ2).1 hz
    · exact ((hN τ).resolve_left hτ1 |>.resolve_left hτ2).2 hz

/-- **The realized orbit is quote-closed**: if quotation has core
    order d and each κ∘sᵐ (m < d) is realized by a judge, then the
    quote-precomposition of every orbit member is again realized —
    modular arithmetic on the orbit. -/
theorem orbit_quote_closure (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ s κ : Fin n)
    (d : Nat) (_hd : 1 ≤ d)
    (hord : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → actPow n dot s d x = x)
    (horb : ∀ m : Nat, m < d → ∃ t : Fin n,
      (t ≠ z₁ ∧ t ≠ z₂ ∧ ClsSide n dot z₁ z₂ t) ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
        dot t x = dot κ (actPow n dot s m x)) :
    ∀ m : Nat, m < d → ∃ t' : Fin n,
      (t' ≠ z₁ ∧ t' ≠ z₂ ∧ ClsSide n dot z₁ z₂ t') ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
        dot t' x = dot κ (actPow n dot s m (dot s x)) := by
  intro m hm
  by_cases hcase : m + 1 < d
  · obtain ⟨t', ht', hact⟩ := horb (m + 1) hcase
    refine ⟨t', ht', fun x hx1 hx2 => ?_⟩
    rw [hact x hx1 hx2, actPow_shift]
  · have hmd : m + 1 = d := by omega
    obtain ⟨t', ht', hact⟩ := horb 0 (by omega)
    refine ⟨t', ht', fun x hx1 hx2 => ?_⟩
    rw [hact x hx1 hx2, ← actPow_shift, hmd, hord x hx1 hx2]
    rfl

/-- **The realized orbit is eval-closed too**: the eval-precomposition
    of κ∘sᵐ is κ∘sᵐ⁻¹ (and κ∘r wraps around to κ∘s^{d-1}). -/
theorem orbit_eval_closure (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ s r : Fin n) (hrN : NclSide n dot z₁ z₂ r)
    (hsr : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot s (dot r x) = x)
    (κ : Fin n) (d : Nat) (hd : 1 ≤ d)
    (hord : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → actPow n dot s d x = x)
    (horb : ∀ m : Nat, m < d → ∃ t : Fin n,
      (t ≠ z₁ ∧ t ≠ z₂ ∧ ClsSide n dot z₁ z₂ t) ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
        dot t x = dot κ (actPow n dot s m x)) :
    ∀ m : Nat, m < d → ∃ t' : Fin n,
      (t' ≠ z₁ ∧ t' ≠ z₂ ∧ ClsSide n dot z₁ z₂ t') ∧
      ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
        dot t' x = dot κ (actPow n dot s m (dot r x)) := by
  intro m hm
  rcases m with _ | k
  · -- κ ∘ r wraps to κ ∘ s^{d-1}
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨t', ht', hact⟩ := horb d' (by omega)
    refine ⟨t', ht', fun x hx1 hx2 => ?_⟩
    have hrx : dot r x ≠ z₁ ∧ dot r x ≠ z₂ :=
      ((hrN x).resolve_left hx1).resolve_left hx2
    rw [hact x hx1 hx2]
    show dot κ (actPow n dot s d' x) = dot κ (actPow n dot s 0 (dot r x))
    rw [show actPow n dot s 0 (dot r x) = dot r x from rfl,
      ← hord (dot r x) hrx.1 hrx.2, actPow_shift, hsr x hx1 hx2]
  · -- (κ ∘ s^{k+1}) ∘ r = κ ∘ s^k
    obtain ⟨t', ht', hact⟩ := horb k (by omega)
    refine ⟨t', ht', fun x hx1 hx2 => ?_⟩
    rw [hact x hx1 hx2, actPow_shift, hsr x hx1 hx2]

end Dichotomic

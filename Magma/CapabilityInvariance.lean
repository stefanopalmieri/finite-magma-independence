import Magma.E2PM

/-!
# Capability Invariance

All three capabilities R, D, and H are preserved by absorber-preserving
isomorphisms of the base structure (extensional 2-pointed magmas).
R, D, and H are intrinsic algebraic properties, not presentation artifacts.

## Results

- `E2PMIso.preserves_retractPair`: R is invariant.
- `E2PMIso.preserves_dichotomy`: D is invariant.
- `E2PMIso.preserves_icp`: H is invariant.
- `E2PMIso.preserves_all`: All three simultaneously.

All proofs are purely algebraic — no `decide`, no `native_decide`.
-/

set_option autoImplicit false

namespace KripkeWall

/-- An isomorphism of extensional 2-pointed magmas: a bijective
    operation-preserving map that sends absorbers to absorbers. -/
structure E2PMIso (n : Nat)
    (dot₁ dot₂ : Fin n → Fin n → Fin n)
    (z₁₁ z₂₁ z₁₂ z₂₂ : Fin n) where
  toFun : Fin n → Fin n
  bij : Function.Bijective toFun
  hom : ∀ a b : Fin n, toFun (dot₁ a b) = dot₂ (toFun a) (toFun b)
  map_z₁ : toFun z₁₁ = z₁₂
  map_z₂ : toFun z₂₁ = z₂₂

-- ═══════════════════════════════════════════════════════════════════
-- R is invariant
-- ═══════════════════════════════════════════════════════════════════

/-- **R is an isomorphism invariant.** If M₁ has a retraction pair,
    then so does M₂. -/
theorem E2PMIso.preserves_retractPair {n : Nat}
    {dot₁ dot₂ : Fin n → Fin n → Fin n} {z₁₁ z₂₁ z₁₂ z₂₂ : Fin n}
    (φ : E2PMIso n dot₁ dot₂ z₁₁ z₂₁ z₁₂ z₂₂) :
    HasRetractPair n dot₁ z₁₁ z₂₁ → HasRetractPair n dot₂ z₁₂ z₂₂ := by
  intro ⟨sec, ret, hret_sec, hsec_ret, hret_z₁⟩
  refine ⟨φ.toFun sec, φ.toFun ret, ?_, ?_, ?_⟩
  · intro x hx₁ hx₂
    obtain ⟨y, rfl⟩ := φ.bij.2 x
    have hy₁ : y ≠ z₁₁ := fun h => hx₁ (by rw [h, φ.map_z₁])
    have hy₂ : y ≠ z₂₁ := fun h => hx₂ (by rw [h, φ.map_z₂])
    rw [← φ.hom, ← φ.hom]
    exact congrArg φ.toFun (hret_sec y hy₁ hy₂)
  · intro x hx₁ hx₂
    obtain ⟨y, rfl⟩ := φ.bij.2 x
    have hy₁ : y ≠ z₁₁ := fun h => hx₁ (by rw [h, φ.map_z₁])
    have hy₂ : y ≠ z₂₁ := fun h => hx₂ (by rw [h, φ.map_z₂])
    rw [← φ.hom, ← φ.hom]
    exact congrArg φ.toFun (hsec_ret y hy₁ hy₂)
  · have := congrArg φ.toFun hret_z₁
    rw [φ.hom] at this
    simp only [φ.map_z₁] at this
    exact this

-- ═══════════════════════════════════════════════════════════════════
-- D is invariant
-- ═══════════════════════════════════════════════════════════════════

/-- **D is an isomorphism invariant.** If M₁ satisfies the classifier
    dichotomy, then so does M₂. -/
theorem E2PMIso.preserves_dichotomy {n : Nat}
    {dot₁ dot₂ : Fin n → Fin n → Fin n} {z₁₁ z₂₁ z₁₂ z₂₂ : Fin n}
    (φ : E2PMIso n dot₁ dot₂ z₁₁ z₂₁ z₁₂ z₂₂) :
    HasDichotomy n dot₁ z₁₁ z₂₁ → HasDichotomy n dot₂ z₁₂ z₂₂ := by
  intro ⟨⟨cls, hcne₁, hcne₂, hcls⟩, hdich, ⟨nd, hnd₁, hnd₂, nx, hnx₁, hnx₂, hnv₁, hnv₂⟩⟩
  refine ⟨⟨φ.toFun cls, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h; exact hcne₁ (φ.bij.1 (by rw [h, φ.map_z₁]))
  · intro h; exact hcne₂ (φ.bij.1 (by rw [h, φ.map_z₂]))
  · intro x
    obtain ⟨y, rfl⟩ := φ.bij.2 x
    rw [← φ.hom]
    cases hcls y with
    | inl h => left; rw [h, φ.map_z₁]
    | inr h => right; rw [h, φ.map_z₂]
  · intro y
    obtain ⟨u, rfl⟩ := φ.bij.2 y
    rcases hdich u with hu | hu | hu | hu
    · left; rw [hu, φ.map_z₁]
    · right; left; rw [hu, φ.map_z₂]
    · right; right; left
      intro x
      obtain ⟨v, rfl⟩ := φ.bij.2 x
      rcases hu v with h | h | h
      · left; rw [h, φ.map_z₁]
      · right; left; rw [h, φ.map_z₂]
      · rw [← φ.hom]
        cases h with
        | inl h => right; right; left; rw [h, φ.map_z₁]
        | inr h => right; right; right; rw [h, φ.map_z₂]
    · right; right; right
      intro x
      obtain ⟨v, rfl⟩ := φ.bij.2 x
      rcases hu v with h | h | ⟨h1, h2⟩
      · left; rw [h, φ.map_z₁]
      · right; left; rw [h, φ.map_z₂]
      · right; right
        rw [← φ.hom]
        exact ⟨fun h => h1 (φ.bij.1 (by rw [h, φ.map_z₁])),
               fun h => h2 (φ.bij.1 (by rw [h, φ.map_z₂]))⟩
  · refine ⟨φ.toFun nd,
      fun h => hnd₁ (φ.bij.1 (by rw [h, φ.map_z₁])),
      fun h => hnd₂ (φ.bij.1 (by rw [h, φ.map_z₂])),
      φ.toFun nx,
      fun h => hnx₁ (φ.bij.1 (by rw [h, φ.map_z₁])),
      fun h => hnx₂ (φ.bij.1 (by rw [h, φ.map_z₂])),
      ?_, ?_⟩
    · rw [← φ.hom]
      exact fun h => hnv₁ (φ.bij.1 (by rw [h, φ.map_z₁]))
    · rw [← φ.hom]
      exact fun h => hnv₂ (φ.bij.1 (by rw [h, φ.map_z₂]))

-- ═══════════════════════════════════════════════════════════════════
-- H is invariant
-- ═══════════════════════════════════════════════════════════════════

/-- **H is an isomorphism invariant.** If M₁ satisfies the ICP,
    then so does M₂. -/
theorem E2PMIso.preserves_icp {n : Nat}
    {dot₁ dot₂ : Fin n → Fin n → Fin n} {z₁₁ z₂₁ z₁₂ z₂₂ : Fin n}
    (φ : E2PMIso n dot₁ dot₂ z₁₁ z₂₁ z₁₂ z₂₂) :
    HasICP n dot₁ z₁₁ z₂₁ → HasICP n dot₂ z₁₂ z₂₂ := by
  intro ⟨a, b, c, hab, hac, hbc, ha1, ha2, hb1, hb2, hc1, hc2,
         hpres, hfact, ⟨x, y, hx1, hx2, hy1, hy2, hneq⟩⟩
  refine ⟨φ.toFun a, φ.toFun b, φ.toFun c,
    fun h => hab (φ.bij.1 h), fun h => hac (φ.bij.1 h), fun h => hbc (φ.bij.1 h),
    fun h => ha1 (φ.bij.1 (by rw [h, φ.map_z₁])),
    fun h => ha2 (φ.bij.1 (by rw [h, φ.map_z₂])),
    fun h => hb1 (φ.bij.1 (by rw [h, φ.map_z₁])),
    fun h => hb2 (φ.bij.1 (by rw [h, φ.map_z₂])),
    fun h => hc1 (φ.bij.1 (by rw [h, φ.map_z₁])),
    fun h => hc2 (φ.bij.1 (by rw [h, φ.map_z₂])),
    ?_, ?_, ⟨φ.toFun x, φ.toFun y, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- b preserves core
    intro u
    obtain ⟨v, rfl⟩ := φ.bij.2 u
    by_cases hv1 : v = z₁₁
    · left; rw [hv1, φ.map_z₁]
    · by_cases hv2 : v = z₂₁
      · right; left; rw [hv2, φ.map_z₂]
      · right; right
        rw [← φ.hom]
        rcases hpres v with h | h | ⟨h1, h2⟩
        · exact absurd h hv1
        · exact absurd h hv2
        · exact ⟨fun h => h1 (φ.bij.1 (by rw [h, φ.map_z₁])),
                 fun h => h2 (φ.bij.1 (by rw [h, φ.map_z₂]))⟩
  · -- Factorization
    intro u
    obtain ⟨v, rfl⟩ := φ.bij.2 u
    by_cases hv1 : v = z₁₁
    · left; rw [hv1, φ.map_z₁]
    · by_cases hv2 : v = z₂₁
      · right; left; rw [hv2, φ.map_z₂]
      · right; right
        rw [← φ.hom, ← φ.hom, ← φ.hom]
        rcases hfact v with h | h | h
        · exact absurd h hv1
        · exact absurd h hv2
        · rw [h]
  · exact fun h => hx1 (φ.bij.1 (by rw [h, φ.map_z₁]))
  · exact fun h => hx2 (φ.bij.1 (by rw [h, φ.map_z₂]))
  · exact fun h => hy1 (φ.bij.1 (by rw [h, φ.map_z₁]))
  · exact fun h => hy2 (φ.bij.1 (by rw [h, φ.map_z₂]))
  · rw [← φ.hom, ← φ.hom]
    exact fun h => hneq (φ.bij.1 h)

-- ═══════════════════════════════════════════════════════════════════
-- Combined: all three capabilities are invariants
-- ═══════════════════════════════════════════════════════════════════

/-- **Capability Invariance.** All three capabilities R, D, and H are
    preserved by absorber-preserving isomorphisms. They are intrinsic
    algebraic properties of finite extensional 2-pointed magmas.
    Algebraic proof, no `decide`. -/
theorem E2PMIso.preserves_all {n : Nat}
    {dot₁ dot₂ : Fin n → Fin n → Fin n} {z₁₁ z₂₁ z₁₂ z₂₂ : Fin n}
    (φ : E2PMIso n dot₁ dot₂ z₁₁ z₂₁ z₁₂ z₂₂) :
    (HasRetractPair n dot₁ z₁₁ z₂₁ → HasRetractPair n dot₂ z₁₂ z₂₂) ∧
    (HasDichotomy n dot₁ z₁₁ z₂₁ → HasDichotomy n dot₂ z₁₂ z₂₂) ∧
    (HasICP n dot₁ z₁₁ z₂₁ → HasICP n dot₂ z₁₂ z₂₂) :=
  ⟨φ.preserves_retractPair, φ.preserves_dichotomy, φ.preserves_icp⟩

end KripkeWall

import Magma.Dichotomic
import Magma.E2PM
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The Completeness Wall: Combinatorial Completeness Excludes the Dichotomy

Three "wall" theorems delimiting the setting of this repository from
the world of combinatory algebras and the λ-calculus (no `Fin n`, no
`decide`; the second holds at arbitrary cardinality, the first and
third are finite by necessity):

1. **K-infinity** (`k_collapse_of_finite`, `no_k_combinator_on_fin`):
   a total magma on a finite carrier with ≥ 2 elements admits no
   $\mathbf{k}$-combinator. Finiteness excludes completeness.

2. **The completeness wall** (`flip_blocks_dichotomy`,
   `sk_blocks_dichotomy`): a total applicative structure of *any*
   cardinality with two left absorbers and $\mathbf{s}, \mathbf{k}$
   combinators cannot satisfy the classifier dichotomy. Completeness
   excludes the dichotomy.

3. **The finite flip wall** (`flip_orbit_collapse`,
   `flip_collapse_of_finite`, `finite_leaves_a_column_unnamed`): a
   total magma on a finite carrier with two *distinct* left absorbers
   cannot internalize every column as a row — at finite scale the
   transposition hypothesis of wall 2 is itself unsatisfiable, with no
   dichotomy in sight. Two halt channels alone refuse the flip.
   (Found 2026-08-03 while testing wall 2 against Lawvere's
   fixed-point theorem; see `docs/lawvere-diagonal-and-the-walls.md`.
   Probe: `scripts/canonicality/probe_flip_absorbers.py` — UNSAT for
   n ≤ 8, and the canonical N=8 artifact names none of its columns.)

Together: finite worlds cannot be combinatorially complete — with two
halt channels they cannot even name their own columns — and complete
worlds cannot be dichotomic. The finite dichotomic magmas of this
repository live strictly below combinatorial completeness — and that is
not an artifact of finiteness, since the second wall stands at every
cardinality (the λ-calculus with two sinks satisfies the flip, so the
third wall is finite by necessity, exactly like the first).

## The transposition argument

The dichotomy D constrains *rows* of the Cayley table: every core row is
absorber-valued or core-valued on the core, never mixed. But D's own
non-degeneracy axioms hand us a mixed *column*: for a classifier τ and a
non-classifier witness y₀ ⬝ x₀ ∉ {z₁, z₂}, the column of x₀ contains
the absorber-valued entry τ ⬝ x₀ and the core-valued entry y₀ ⬝ x₀.
A mixed column is harmless — D says nothing about columns — until the
structure can *transpose*: an element `m` with `m ⬝ x = x ⬝ x₀` for all
`x` has the column of x₀ as its row, and is therefore a mixed core
element, contradicting D. Combinatorial completeness provides such an
`m` for every x₀ (the thrush `λx. x ⬝ x₀`, definable as
`s ⬝ (s ⬝ k ⬝ k) ⬝ (k ⬝ x₀)`), so D fails. The dichotomy is consistent
exactly in worlds that cannot internalize their own columns as rows.

Read in the λ-calculus (with two absorbing sink constants) or in the
λ̄μμ̃-calculus (where absorbers are aborting terms μ_.c and classifiers
are total deciders): splitting S and composition C are definable for
free, but the dichotomy provably fails — mixed elements ("partial
deciders", programs that abort on some inputs and return on others) are
always definable. The S/D/C landscape of this paper is the regime that
computational completeness forbids.

Neither extensionality nor `no_other_zeros` is used in any wall; the
distinctness of the two absorbers is used only in the third (where it
must be: with `z₁ = z₂` a one-absorber commutative-looking flip is not
obstructed).
-/

set_option autoImplicit false

namespace Dichotomic

/-- The classifier dichotomy on an arbitrary carrier — verbatim the
    `HasDichotomy` of `E2PM.lean` with `Fin n` generalized to `A`, so it
    can be stated for infinite applicative structures (term models of
    the λ-calculus, combinatory algebras). -/
@[reducible] def HasDichotomyOn {A : Type*} (dot : A → A → A) (z₁ z₂ : A) : Prop :=
  -- A classifier exists
  (∃ cls : A, cls ≠ z₁ ∧ cls ≠ z₂ ∧
    ∀ x : A, dot cls x = z₁ ∨ dot cls x = z₂) ∧
  -- The dichotomy holds (disjunction form)
  (∀ y : A, y = z₁ ∨ y = z₂ ∨
    (∀ x : A, x = z₁ ∨ x = z₂ ∨ (dot y x = z₁ ∨ dot y x = z₂)) ∨
    (∀ x : A, x = z₁ ∨ x = z₂ ∨ (dot y x ≠ z₁ ∧ dot y x ≠ z₂))) ∧
  -- Non-degeneracy: a non-classifier exists
  (∃ y : A, y ≠ z₁ ∧ y ≠ z₂ ∧
    ∃ x : A, x ≠ z₁ ∧ x ≠ z₂ ∧ dot y x ≠ z₁ ∧ dot y x ≠ z₂)

/-- On `Fin n` the generalized dichotomy coincides definitionally with
    the `HasDichotomy` of `E2PM.lean`. -/
theorem hasDichotomyOn_fin_iff (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) :
    HasDichotomyOn dot z₁ z₂ ↔ HasDichotomy n dot z₁ z₂ :=
  Iff.rfl

-- ═══════════════════════════════════════════════════════════════════
-- Wall 1: K-infinity (finiteness excludes completeness)
-- ═══════════════════════════════════════════════════════════════════

/-- **K-infinity, collapse form.** A total magma on a finite carrier
    with a k-combinator is a subsingleton. (Contrapositive of the
    paper's Theorem "K-infinity": a nontrivial total magma with
    $\mathbf{k}$ is infinite.) The proof is the paper's: `dot k ·` is
    injective, finiteness makes it surjective, and a preimage of `k`
    forces `dot k ·` to be constant. -/
theorem k_collapse_of_finite {A : Type*} [Finite A] (dot : A → A → A) (k : A)
    (hk : ∀ a b : A, dot (dot k a) b = a) : Subsingleton A := by
  have hinj : Function.Injective (fun x => dot k x) := by
    intro a b h
    calc a = dot (dot k a) a := (hk a a).symm
      _ = dot (dot k b) a := by simp only at h; rw [h]
      _ = b := hk b a
  have hsurj : Function.Surjective (fun x => dot k x) :=
    Finite.surjective_of_injective hinj
  obtain ⟨w, hw⟩ := hsurj k
  simp only at hw
  -- with dot k w = k, every column of k is w
  have hconst : ∀ y : A, dot k y = w := by
    intro y
    calc dot k y = dot (dot k w) y := by rw [hw]
      _ = w := hk w y
  exact ⟨fun a b => hinj (by simp only; rw [hconst a, hconst b])⟩

/-- **K-infinity on `Fin n`**: no total magma on `n ≥ 2` elements
    admits a k-combinator. This is the form that motivates the setting
    of this repository: finite carriers cannot be combinatorially
    complete, so the direct finite analogue of a PCA/TCA does not
    exist. -/
theorem no_k_combinator_on_fin (n : Nat) (hn : 2 ≤ n)
    (dot : Fin n → Fin n → Fin n) :
    ¬ ∃ k : Fin n, ∀ a b : Fin n, dot (dot k a) b = a := by
  rintro ⟨k, hk⟩
  haveI : Finite (Fin n) := Finite.intro (Equiv.refl _)
  have hsub := k_collapse_of_finite dot k hk
  have h01 : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := hsub.allEq _ _
  have h01' : (0 : Nat) = 1 := congrArg Fin.val h01
  omega

-- ═══════════════════════════════════════════════════════════════════
-- Wall 2: the completeness wall (completeness excludes the dichotomy)
-- ═══════════════════════════════════════════════════════════════════

/-- **The transposition lemma.** If every column of the Cayley table is
    internalized as a row — for every `a` there is an element `m` with
    `m ⬝ x = x ⬝ a` for all `x` — then the classifier dichotomy fails.
    D's own axioms provide a mixed column (the classifier τ and the
    non-classifier witness y₀ both evaluated at x₀); transposition
    imports it into the row space as a mixed element. Works at any
    cardinality; extensionality is not needed; only the two
    left-absorption laws are used. -/
theorem flip_blocks_dichotomy {A : Type*} (dot : A → A → A) (z₁ z₂ : A)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂)
    (hflip : ∀ a : A, ∃ m : A, ∀ x : A, dot m x = dot x a) :
    ¬ HasDichotomyOn dot z₁ z₂ := by
  rintro ⟨⟨τ, hτ1, hτ2, hτbool⟩, hdich, y₀, hy1, hy2, x₀, hx1, hx2, hne1, hne2⟩
  obtain ⟨m, hm⟩ := hflip x₀
  -- m's row is the column of x₀: absorber-valued at τ, core-valued at y₀
  have hmix_bool : dot m τ = z₁ ∨ dot m τ = z₂ := by
    rw [hm τ]; exact hτbool x₀
  have hmix_core : dot m y₀ ≠ z₁ ∧ dot m y₀ ≠ z₂ := by
    rw [hm y₀]; exact ⟨hne1, hne2⟩
  -- m is not an absorber (its row takes a core value at y₀)
  have hm1 : m ≠ z₁ := fun h => hmix_core.1 (by rw [h, hz₁])
  have hm2 : m ≠ z₂ := fun h => hmix_core.2 (by rw [h, hz₂])
  -- so the dichotomy classifies m, and both sides fail
  rcases hdich m with h | h | h | h
  · exact hm1 h
  · exact hm2 h
  · -- classifier side fails at y₀
    rcases h y₀ with h' | h' | h'
    · exact hy1 h'
    · exact hy2 h'
    · rcases h' with h' | h'
      · exact hmix_core.1 h'
      · exact hmix_core.2 h'
  · -- non-classifier side fails at τ
    rcases h τ with h' | h' | h'
    · exact hτ1 h'
    · exact hτ2 h'
    · rcases hmix_bool with hb | hb
      · exact h'.1 hb
      · exact h'.2 hb

/-- S and K internalize every column: `s ⬝ (s ⬝ k ⬝ k) ⬝ (k ⬝ a)` is the
    thrush `λx. x ⬝ a`. -/
theorem sk_flip {A : Type*} (dot : A → A → A) (k s : A)
    (hk : ∀ a b : A, dot (dot k a) b = a)
    (hs : ∀ a b c : A, dot (dot (dot s a) b) c = dot (dot a c) (dot b c))
    (a : A) : ∃ m : A, ∀ x : A, dot m x = dot x a := by
  refine ⟨dot (dot s (dot (dot s k) k)) (dot k a), fun x => ?_⟩
  calc dot (dot (dot s (dot (dot s k) k)) (dot k a)) x
      = dot (dot (dot (dot s k) k) x) (dot (dot k a) x) := hs _ _ _
    _ = dot (dot (dot (dot s k) k) x) a := by rw [hk]
    _ = dot (dot (dot k x) (dot k x)) a := by rw [hs]
    _ = dot x a := by rw [hk]

/-- **The completeness wall.** No total applicative structure — of any
    cardinality — with two left absorbers and $\mathbf{s}, \mathbf{k}$
    combinators satisfies the classifier dichotomy. In particular the
    term models of the untyped λ-calculus (or λ̄μμ̃-calculus) extended
    with two absorbing sinks satisfy S and C but can never satisfy D:
    the S/D/C landscape of this repository is the regime that
    combinatorial completeness forbids, at every cardinality. -/
theorem sk_blocks_dichotomy {A : Type*} (dot : A → A → A) (z₁ z₂ k s : A)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂)
    (hk : ∀ a b : A, dot (dot k a) b = a)
    (hs : ∀ a b c : A, dot (dot (dot s a) b) c = dot (dot a c) (dot b c)) :
    ¬ HasDichotomyOn dot z₁ z₂ :=
  flip_blocks_dichotomy dot z₁ z₂ hz₁ hz₂ (sk_flip dot k s hk hs)

/-- Contrapositive of `flip_blocks_dichotomy`, in representation-theoretic
    vocabulary: **in every dichotomic 2-pointed applicative structure — of
    any cardinality — the right regular representation is not contained in
    the image of the left regular representation**: some column is named by
    no row. This is the sharp, counting-free form of the completeness wall
    (only |A| columns need naming, so no cardinality argument applies), and
    the recommended expert-facing statement. -/
theorem d_leaves_a_column_unnamed {A : Type*} (dot : A → A → A) (z₁ z₂ : A)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂)
    (hD : HasDichotomyOn dot z₁ z₂) :
    ∃ a : A, ¬ ∃ m : A, ∀ x : A, dot m x = dot x a := by
  by_contra h
  push_neg at h
  exact flip_blocks_dichotomy dot z₁ z₂ hz₁ hz₂ h hD

-- ═══════════════════════════════════════════════════════════════════
-- Wall 3: the finite flip wall (two absorbers exclude column-naming)
-- ═══════════════════════════════════════════════════════════════════

/-- **Descent engine for the finite flip wall.** Given a naming
    operator ν (`ν a` internalizes the column of `a` as a row), a
    repeat in the ν-orbit of `z₁` at positive indices collapses the two
    absorbers. The descent: column-agreement of two orbit points at
    height `j + 1` becomes row-agreement (evaluate the columns at
    names, which transposes), which becomes column-agreement at height
    `j`; at height `0` the row of the orbit point at height `p + 1` is
    revealed to be constant `z₁`, while every ν-image must fix `z₂`.
    No finiteness is used here — finiteness only supplies the repeat.
    No self-application is formed anywhere: the engine is
    transposition and orbit-periodicity, not diagonalization. -/
theorem flip_orbit_collapse {A : Type*} (dot : A → A → A) (z₁ z₂ : A)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂)
    (ν : A → A) (hν : ∀ a x : A, dot (ν a) x = dot x a)
    (k p : ℕ) (hrep : ν^[k + 1] z₁ = ν^[k + 1 + (p + 1)] z₁) :
    z₁ = z₂ := by
  have hsucc : ∀ j : ℕ, ν^[j + 1] z₁ = ν (ν^[j] z₁) := fun j =>
    Function.iterate_succ_apply' ν j z₁
  -- columns agreeing at height j forces rows agreeing at height j
  have rows_of_cols : ∀ j : ℕ,
      (∀ x, dot x (ν^[j] z₁) = dot x (ν^[j + (p + 1)] z₁)) →
      ∀ b, dot (ν^[j] z₁) b = dot (ν^[j + (p + 1)] z₁) b := by
    intro j hc b
    have h := hc (ν b)
    rwa [hν b (ν^[j] z₁), hν b (ν^[j + (p + 1)] z₁)] at h
  -- and rows agreeing at height j + 1 forces columns agreeing at j
  have cols_step : ∀ j : ℕ,
      (∀ x, dot x (ν^[j + 1] z₁) = dot x (ν^[j + 1 + (p + 1)] z₁)) →
      ∀ x, dot x (ν^[j] z₁) = dot x (ν^[j + (p + 1)] z₁) := by
    intro j hc x
    have hr := rows_of_cols (j + 1) hc x
    have e : j + 1 + (p + 1) = j + (p + 1) + 1 := by omega
    rw [hsucc j, e, hsucc (j + (p + 1))] at hr
    rwa [hν (ν^[j] z₁) x, hν (ν^[j + (p + 1)] z₁) x] at hr
  -- the repeat seeds the descent at height k
  have base : ∀ x, dot x (ν^[k] z₁) = dot x (ν^[k + (p + 1)] z₁) := by
    refine cols_step k fun x => ?_
    rw [hrep]
  -- descend to height 0
  have cols0 : ∀ x, dot x (ν^[0] z₁) = dot x (ν^[0 + (p + 1)] z₁) := by
    have desc : ∀ j : ℕ,
        (∀ x, dot x (ν^[j] z₁) = dot x (ν^[j + (p + 1)] z₁)) →
        ∀ x, dot x (ν^[0] z₁) = dot x (ν^[0 + (p + 1)] z₁) := by
      intro j
      induction j with
      | zero => exact fun h => h
      | succ n ih => exact fun h => ih (cols_step n h)
    exact desc k base
  -- endgame: the row of the height-(p+1) point is constant z₁,
  -- yet as a ν-image it must send z₂ to z₂
  have h := rows_of_cols 0 cols0 z₂
  rw [Function.iterate_zero_apply, hz₁ z₂] at h
  have e : 0 + (p + 1) = p + 1 := by omega
  rw [e, hsucc p, hν (ν^[p] z₁) z₂, hz₂ (ν^[p] z₁)] at h
  exact h

/-- **The finite flip wall, collapse form.** A total magma on a finite
    carrier with two left absorbers that internalizes every column as a
    row identifies the two absorbers. Contrapositive: with `z₁ ≠ z₂`,
    the transposition hypothesis of `flip_blocks_dichotomy` is not
    merely dichotomy-blocking but *unsatisfiable* — at finite scale the
    completeness wall needs no dichotomy. At infinite cardinality the
    hypothesis is satisfiable (the λ-calculus with two sinks has the
    thrush), so wall 2 remains the sharp statement there: finiteness is
    essential, exactly as in K-infinity, and the engine is the same
    pigeonhole species — a finite orbit must repeat, and transposition
    turns the repeat into a constant row. -/
theorem flip_collapse_of_finite {A : Type*} [Finite A] (dot : A → A → A)
    (z₁ z₂ : A)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂)
    (hflip : ∀ a : A, ∃ m : A, ∀ x : A, dot m x = dot x a) :
    z₁ = z₂ := by
  choose ν hν using hflip
  obtain ⟨i, j, hij, hrep⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun t : ℕ => ν^[t + 1] z₁)
  have hrep' : ν^[i + 1] z₁ = ν^[j + 1] z₁ := hrep
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine flip_orbit_collapse dot z₁ z₂ hz₁ hz₂ ν hν i (j - i - 1) ?_
    have e : i + 1 + (j - i - 1 + 1) = j + 1 := by omega
    rw [e]
    exact hrep'
  · refine flip_orbit_collapse dot z₁ z₂ hz₁ hz₂ ν hν j (i - j - 1) ?_
    have e : j + 1 + (i - j - 1 + 1) = i + 1 := by omega
    rw [e]
    exact hrep'.symm

/-- **The finite flip wall, unnamed-column form.** Every finite magma
    with two *distinct* left absorbers leaves some column named by no
    row: the finite counterpart of `d_leaves_a_column_unnamed`, with
    the dichotomy hypothesis deleted. (The canonical N=8 artifact
    leaves all eight of its columns unnamed —
    `scripts/canonicality/probe_flip_absorbers.py`.) -/
theorem finite_leaves_a_column_unnamed {A : Type*} [Finite A]
    (dot : A → A → A) (z₁ z₂ : A) (hz : z₁ ≠ z₂)
    (hz₁ : ∀ x : A, dot z₁ x = z₁) (hz₂ : ∀ x : A, dot z₂ x = z₂) :
    ∃ a : A, ¬ ∃ m : A, ∀ x : A, dot m x = dot x a := by
  by_contra h
  push_neg at h
  exact hz (flip_collapse_of_finite dot z₁ z₂ hz₁ hz₂ h)

/-- The two walls, packaged for the finite setting: on `Fin n` with
    `n ≥ 2`, the completeness hypothesis of `sk_blocks_dichotomy` is
    itself unsatisfiable — already the k-combinator alone is impossible.
    Finite worlds cannot be complete; complete worlds cannot be
    dichotomic; the finite dichotomic magmas of this repository live
    strictly below combinatorial completeness. -/
theorem walls_are_complementary (n : Nat) (hn : 2 ≤ n)
    (dot : Fin n → Fin n → Fin n) :
    ¬ ∃ k s : Fin n,
      (∀ a b : Fin n, dot (dot k a) b = a) ∧
      (∀ a b c : Fin n, dot (dot (dot s a) b) c = dot (dot a c) (dot b c)) := by
  rintro ⟨k, s, hk, -⟩
  exact no_k_combinator_on_fin n hn dot ⟨k, hk⟩

end Dichotomic

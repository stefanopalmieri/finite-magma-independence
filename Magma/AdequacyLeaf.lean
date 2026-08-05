import Magma.AdequacyStartup
import Magma.AdequacyInstances
import Mathlib.Tactic.FinCases

/-!
# Adequacy campaign, rung 3b(ii): the leaf forms, universally

Adequacy for the two leaf syntax classes, closed over their *entire*
domains — the campaign's first universal adequacy theorems:

* **Atoms** (`adequacy_atom`): all eight, by `fin_cases` and native
  execution. The observed pairing `(quo . k) ~ elem k` for every `k`
  is the certified retraction `eatom ∘ qatom = id` showing through
  the interpreter: META's atom branch recomputes, via the tag trees,
  exactly the element the machine evaluates the atom to.

* **Variables** (`adequacy_var`): all `n : Nat` — an *infinite*
  class, closed **symbolically by kernel reduction**. The top-level
  object environment is `tt`, and `mnth` tests `pair? env` before
  ever touching the index, so the 144-step interpreted run never
  inspects the numeral: `n` rides through the whole computation as a
  passenger, and one `rfl` covers every index. Both worlds miss, and
  the two miss values are related — the error-default agreement of
  rung 2 (`RepEnv.chainNth`), now a universal theorem at the top
  level.

With `meval_entry` discharging the knot uniformly, each leaf theorem
is: entry (`entrySteps`), then a concrete-count interpreted epilogue,
against a two-step direct run. Fuel is exact on the meta side —
`loop (varSteps + entrySteps)` — because the fuel-transfer lemmas
make the counts compose.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyLeaf

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep

/-- A completed `stepIter` that produced a value is a successful
    `loop` at the same fuel. -/
theorem loop_of_stepIter_inr {n : Nat} {s : State} {v : Val}
    (h : stepIter n s = .inr v) : loop n s = some v := by
  induction n generalizing s with
  | zero => simp [stepIter] at h
  | succ n ih =>
    simp only [stepIter] at h
    simp only [loop]
    cases hs : step s with
    | inl s' => rw [hs] at h; exact ih h
    | inr w => rw [hs] at h; cases h; rfl

/-! ## Variables: an infinite class, one kernel reduction -/

/-- The interpreted variable run takes exactly this many steps from
    the `meval` entry — independent of the index. -/
def varSteps : Nat := 144

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **The symbolic variable run**: for *every* `n`, the interpreted
    run misses in the empty top-level environment and produces
    META's error default `(quo . tt)` in exactly `varSteps` steps.
    Provable by `rfl` because `mnth` tests the environment before
    the numeral: the index is a passenger. -/
theorem meval_var (n : Nat) :
    stepIter varSteps (mevalEntry (.var n)) =
      .inr (.cell (.elem 2) (.elem 0)) :=
  rfl

/-- The direct variable run misses in the empty environment and
    produces the machine's error default — also symbolically. -/
theorem direct_var (n : Nat) :
    runM 2 [] [] (.var n) = some (.elem 0) :=
  rfl

/-- **Universal adequacy for variables**: for every index, both
    worlds miss, in exact fuel, and the two miss values are
    related. The campaign's first adequacy theorem over an infinite
    syntax class. -/
theorem adequacy_var (n : Nat) :
    loop (varSteps + entrySteps) (metaState (.var n)) =
      some (.cell (.elem 2) (.elem 0)) ∧
    runM 2 [] [] (.var n) = some (.elem 0) ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := by
  refine ⟨?_, direct_var n, .elem 0⟩
  rw [loop_meval_entry (.var n) varSteps]
  exact loop_of_stepIter_inr (meval_var n)

/-! ## Atoms: the whole `Fin 8` class -/

/-- **Universal adequacy for atoms**: all eight, each by native
    execution of the image (in the rung-3a `check` form — `Val` has
    no decidable equality, so run results go through the structural
    comparator), paired by the `RepV.elem` clause. The meta result
    `(quo . k)` against the direct `elem k` is `eatom ∘ qatom = id`
    — the certified retraction, recomputed by the interpreter's tag
    trees. -/
theorem adequacy_atom (k : Fin 8) :
    check (.atom k) (.cell (.elem 2) (.elem k)) (.elem k) = true ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem k)) (.elem k) := by
  fin_cases k <;> exact ⟨by native_decide, .elem _⟩

end AdequacyLeaf
end Dichotomic

import Magma.AdequacyStartup
import Magma.AdequacyInstances
import Mathlib.Tactic.FinCases

/-!
# Adequacy campaign, rung 3b(iii): β through the interpreter, by families

Adequacy for compound programs — applications, closure formation,
β-reduction — closed over infinite *families* by symbolic kernel
reduction. The passenger principle from the leaf rung reaches
surprisingly far into compound programs: an application's entire
dispatch path (`mform` on the app tag, argument evaluation order,
`mapply`'s tag trees, closure entry) is concrete; only the leaf
indices are symbolic, and when the leaves are variables the
interpreted run never inspects them. So:

* `adequacy_beta_var` — `(λx.x) (var n)` for **all** `n`: one `rfl`
  closes an infinite family of β-redexes (760 interpreted steps
  against 7 direct — the ~110× interpretive overhead, constant
  across the family);
* `adequacy_K` — `((λx.λy.x) (var n)) (var m)` for **all** `n, m`:
  a *doubly*-infinite family, two β-reductions and a two-deep
  closure environment, one kernel reduction;
* `adequacy_beta_nested` — `(λx.x) ((λx.x) (var n))`: nested
  redexes, the inner result flowing as the outer argument;
* `adequacy_beta_closure` — `(λx.x) (λx.x)`: a closure *returned
  through* β, landing in the `RepV.clos` clause;
* `adequacy_beta_atom` — `(λx.x) (atom k)`, all eight, by
  `fin_cases` + native execution (`check` form).

Where this rung stops, honestly: these families have concrete
dispatch *skeletons*. Adequacy for `app f x` with `f, x` themselves
universally quantified requires the general simulation induction
(recursive `meval` calls under META's own frames) — rung 3b(iv)'s
business, for which these theorems are the base cases and the
regression net.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyBeta

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep

/-- The identity combinator. -/
def idL : Prog := .lam (.var 0)

/-- The K combinator. -/
def kComb : Prog := .lam (.lam (.var 1))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **β over an infinite family**: the identity applied to any
    variable. The redex fires in the interpreted world — closure
    formed, argument missed (both worlds), body entered, argument
    returned — uniformly in the index. -/
theorem adequacy_beta_var (n : Nat) :
    loop (800 + entrySteps) (metaState (.app idL (.var n))) =
      some (.cell (.elem 2) (.elem 0)) ∧
    runM 20 [] [] (.app idL (.var n)) = some (.elem 0) ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := by
  refine ⟨?_, rfl, .elem 0⟩
  rw [loop_meval_entry (.app idL (.var n)) 800]
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **A doubly-infinite family**: K applied to two variables — two
    β-reductions, a two-deep closure environment, `mnth` at index 1
    through the tagged environment — for *all* `n` and `m`, one
    kernel reduction. -/
theorem adequacy_K (n m : Nat) :
    loop (1500 + entrySteps)
        (metaState (.app (.app kComb (.var n)) (.var m))) =
      some (.cell (.elem 2) (.elem 0)) ∧
    runM 20 [] [] (.app (.app kComb (.var n)) (.var m)) =
      some (.elem 0) ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := by
  refine ⟨?_, rfl, .elem 0⟩
  rw [loop_meval_entry (.app (.app kComb (.var n)) (.var m)) 1500]
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Nested redexes**: the inner application's result flows as the
    outer application's argument, for all `n`. -/
theorem adequacy_beta_nested (n : Nat) :
    loop (1500 + entrySteps)
        (metaState (.app idL (.app idL (.var n)))) =
      some (.cell (.elem 2) (.elem 0)) ∧
    runM 20 [] [] (.app idL (.app idL (.var n))) = some (.elem 0) ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := by
  refine ⟨?_, rfl, .elem 0⟩
  rw [loop_meval_entry (.app idL (.app idL (.var n))) 1500]
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **A closure through β**: the identity applied to itself returns
    a closure value across the redex — the `RepV.clos` clause
    exercised by a compound run (META's result carries exactly
    `quoteD (var 0)` and the nil environment). -/
theorem adequacy_beta_closure :
    loop (800 + entrySteps) (metaState (.app idL idL)) =
      some (.cell (.elem 3)
        (.cell (.cell (.elem 4) (.elem 0)) (.elem 0))) ∧
    runM 20 [] [] (.app idL idL) = some (.clos (.var 0) []) ∧
    RepV 14 KRempty
      (.cell (.elem 3) (.cell (.cell (.elem 4) (.elem 0)) (.elem 0)))
      (.clos (.var 0) []) := by
  refine ⟨?_, rfl, .clos (.var 0) .nil⟩
  rw [loop_meval_entry (.app idL idL) 800]
  rfl

/-- **β delivering every atom**: the identity applied to each of the
    eight atoms (`check` form — `Val` has no decidable equality). -/
theorem adequacy_beta_atom (k : Fin 8) :
    check (.app idL (.atom k))
      (.cell (.elem 2) (.elem k)) (.elem k) = true ∧
    RepV 14 KRempty (.cell (.elem 2) (.elem k)) (.elem k) := by
  fin_cases k <;> exact ⟨by native_decide, .elem _⟩

end AdequacyBeta
end Dichotomic

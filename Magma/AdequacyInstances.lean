import Magma.MetaImage
import Magma.AdequacyRep

/-!
# Adequacy campaign, rung 3a: executable adequacy instances

The Lean-side analogue of the Rust adequacy corpus: end-to-end runs
of the **frozen image** on the certified machine, one instance per
syntax class of the (eqv-free) domain. Each instance is two
theorems:

* `…_runs` — the machine actually executes the ~700-node image inside
  the proof (`native_decide`) and both worlds produce exactly the
  expected literals (checked by the structural comparator `beqV`;
  `Val`/`Kont` admit no derived `DecidableEq` — the deriving handler
  rejects the mutual-with-nested-`List` shape — so run results are
  compared by `beqV`, whose reflexivity is proved below and whose
  soundness is evident from its shape; the *propositional* adequacy
  statements arrive with the universal theorem, which does not pass
  through `beqV` at all);
* `…_rep` — the `RepV` derivation connecting the two literals, by
  constructor: the rung-2 relation's clauses fit the observed values
  on the nose, with no automation.

What the instances pin down empirically, ahead of the universal
proof:

* **error defaults correspond** (`var_unbound`): META's miss value
  `(quo . tt)` represents the machine's miss value `elem 0`, exactly
  as `RepEnv.chainNth` predicted;
* **the store offset works** (`ref_deref`, `setref`): object
  allocations land after the knot prefix and reads/writes route
  correctly through `i ↦ K₀ + i`;
* **host absorption works** (`callcc_throw`): invoking an object
  continuation through META's single host `callcc` produces the
  direct value;
* **closures represent** (`lam_value`): META stores exactly
  `quoteD body` and the nil environment — the `RepV.clos` clause,
  observed.

These theorems are regression armor for every later rung: if the
image, the relation, or the machine drifts, they fail loudly and
first.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyInstances

open FactorizationEqv MetaImage AdequacyRep

/-! ## A structural comparator (no derived equality exists for `Val`) -/

mutual
  def beqV : Val → Val → Bool
    | .elem a, .elem b => a == b
    | .cell a d, .cell a' d' => beqV a a' && beqV d d'
    | .clos p ρ, .clos p' ρ' => p == p' && beqVs ρ ρ'
    | .cont k, .cont k' => beqK k k'
    | .loc n, .loc n' => n == n'
    | _, _ => false

  def beqVs : List Val → List Val → Bool
    | [], [] => true
    | v :: vs, v' :: vs' => beqV v v' && beqVs vs vs'
    | _, _ => false

  def beqK : Kont → Kont → Bool
    | .halt, .halt => true
    | .appL p ρ k, .appL p' ρ' k' => p == p' && beqVs ρ ρ' && beqK k k'
    | .appR v k, .appR v' k' => beqV v v' && beqK k k'
    | .refK k, .refK k' => beqK k k'
    | .derefK k, .derefK k' => beqK k k'
    | .setL p ρ k, .setL p' ρ' k' => p == p' && beqVs ρ ρ' && beqK k k'
    | .setR v k, .setR v' k' => beqV v v' && beqK k k'
    | .consL p ρ k, .consL p' ρ' k' => p == p' && beqVs ρ ρ' && beqK k k'
    | .consR v k, .consR v' k' => beqV v v' && beqK k k'
    | .carK k, .carK k' => beqK k k'
    | .cdrK k, .cdrK k' => beqK k k'
    | .pairK k, .pairK k' => beqK k k'
    | .iteK t e ρ k, .iteK t' e' ρ' k' =>
      t == t' && e == e' && beqVs ρ ρ' && beqK k k'
    | .eqvL p ρ k, .eqvL p' ρ' k' => p == p' && beqVs ρ ρ' && beqK k k'
    | .eqvR v k, .eqvR v' k' => beqV v v' && beqK k k'
    | _, _ => false
end

mutual
  theorem beqV_refl : ∀ v : Val, beqV v v = true
    | .elem a => by simp [beqV]
    | .cell a d => by simp [beqV, beqV_refl a, beqV_refl d]
    | .clos p ρ => by simp [beqV, beqVs_refl ρ]
    | .cont k => by simp [beqV, beqK_refl k]
    | .loc n => by simp [beqV]

  theorem beqVs_refl : ∀ vs : List Val, beqVs vs vs = true
    | [] => by simp [beqVs]
    | v :: vs => by simp [beqVs, beqV_refl v, beqVs_refl vs]

  theorem beqK_refl : ∀ k : Kont, beqK k k = true
    | .halt => by simp [beqK]
    | .appL p ρ k => by simp [beqK, beqVs_refl ρ, beqK_refl k]
    | .appR v k => by simp [beqK, beqV_refl v, beqK_refl k]
    | .refK k => by simp [beqK, beqK_refl k]
    | .derefK k => by simp [beqK, beqK_refl k]
    | .setL p ρ k => by simp [beqK, beqVs_refl ρ, beqK_refl k]
    | .setR v k => by simp [beqK, beqV_refl v, beqK_refl k]
    | .consL p ρ k => by simp [beqK, beqVs_refl ρ, beqK_refl k]
    | .consR v k => by simp [beqK, beqV_refl v, beqK_refl k]
    | .carK k => by simp [beqK, beqK_refl k]
    | .cdrK k => by simp [beqK, beqK_refl k]
    | .pairK k => by simp [beqK, beqK_refl k]
    | .iteK t e ρ k => by simp [beqK, beqVs_refl ρ, beqK_refl k]
    | .eqvL p ρ k => by simp [beqK, beqVs_refl ρ, beqK_refl k]
    | .eqvR v k => by simp [beqK, beqV_refl v, beqK_refl k]
end

/-- Did this meta-side run produce exactly the expected value? -/
def checkM (p : Prog) (expected : Val) : Bool :=
  match loop 200000 (.eval (.app META (.var 0)) [quoteD p] [] .halt) with
  | some v => beqV v expected
  | none => false

/-- Did this direct run produce exactly the expected value? -/
def checkD (p : Prog) (expected : Val) : Bool :=
  match runM 10000 [] [] p with
  | some v => beqV v expected
  | none => false

/-- Both worlds produce their expected literals. -/
def check (p : Prog) (vT v : Val) : Bool :=
  checkM p vT && checkD p v

/-- Empty continuation relation: every instance below produces a
    first-order value, so no continuation ever needs relating. -/
def KRempty : Kont → Kont → Prop := fun _ _ => False

/-- Knot-prefix length: the image's letrec allocates 14 cells. -/
def K₀ : Nat := 14

/-! ## The instances -/

theorem atom_runs :
    check (.atom 0) (.cell (.elem 2) (.elem 0)) (.elem 0) = true := by
  native_decide
theorem atom_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := .elem 0

/-- The error-default instance: an unbound variable misses in both
    worlds, and the two miss values are related. -/
theorem var_unbound_runs :
    check (.var 0) (.cell (.elem 2) (.elem 0)) (.elem 0) = true := by
  native_decide
theorem var_unbound_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := .elem 0

theorem beta_runs :
    check (.app (.lam (.var 0)) (.atom 5))
      (.cell (.elem 2) (.elem 5)) (.elem 5) = true := by
  native_decide
theorem beta_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 5)) (.elem 5) := .elem 5

/-- Two-argument K-combinator chain: nested closures, `mnth` at
    index 1. -/
theorem kcomb_runs :
    check (.app (.app (.lam (.lam (.var 1))) (.atom 5)) (.atom 6))
      (.cell (.elem 2) (.elem 5)) (.elem 5) = true := by
  native_decide
theorem kcomb_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 5)) (.elem 5) := .elem 5

/-- A closure as final value: META stores exactly `quoteD body` and
    the nil environment — the `RepV.clos` clause observed. -/
theorem lam_value_runs :
    check (.lam (.var 0))
      (.cell (.elem 3) (.cell (.cell (.elem 4) (.elem 0)) (.elem 0)))
      (.clos (.var 0) []) = true := by
  native_decide
theorem lam_value_rep :
    RepV K₀ KRempty
      (.cell (.elem 3) (.cell (.cell (.elem 4) (.elem 0)) (.elem 0)))
      (.clos (.var 0) []) := .clos (.var 0) .nil

theorem cons_runs :
    check (.cons (.atom 3) (.atom 5))
      (.cell (.elem 6)
        (.cell (.cell (.elem 2) (.elem 3)) (.cell (.elem 2) (.elem 5))))
      (.cell (.elem 3) (.elem 5)) = true := by
  native_decide
theorem cons_rep :
    RepV K₀ KRempty
      (.cell (.elem 6)
        (.cell (.cell (.elem 2) (.elem 3)) (.cell (.elem 2) (.elem 5))))
      (.cell (.elem 3) (.elem 5)) := .cell (.elem 3) (.elem 5)

theorem car_runs :
    check (.car (.cons (.atom 3) (.atom 5)))
      (.cell (.elem 2) (.elem 3)) (.elem 3) = true := by
  native_decide
theorem car_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 3)) (.elem 3) := .elem 3

theorem cdr_runs :
    check (.cdr (.cons (.atom 3) (.atom 5)))
      (.cell (.elem 2) (.elem 5)) (.elem 5) = true := by
  native_decide
theorem cdr_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 5)) (.elem 5) := .elem 5

/-- Nested projections through a nested pair. -/
theorem cadr_runs :
    check (.car (.cdr (.cons (.atom 2) (.cons (.atom 3) (.atom 4)))))
      (.cell (.elem 2) (.elem 3)) (.elem 3) = true := by
  native_decide
theorem cadr_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 3)) (.elem 3) := .elem 3

theorem pairp_yes_runs :
    check (.pairp (.cons (.atom 3) (.atom 5)))
      (.cell (.elem 2) (.elem 0)) (.elem 0) = true := by
  native_decide
theorem pairp_yes_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 0)) (.elem 0) := .elem 0

theorem pairp_no_runs :
    check (.pairp (.atom 3))
      (.cell (.elem 2) (.elem 1)) (.elem 1) = true := by
  native_decide
theorem pairp_no_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 1)) (.elem 1) := .elem 1

theorem ite_true_runs :
    check (.ite (.atom 0) (.atom 5) (.atom 6))
      (.cell (.elem 2) (.elem 5)) (.elem 5) = true := by
  native_decide
theorem ite_true_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 5)) (.elem 5) := .elem 5

theorem ite_false_runs :
    check (.ite (.atom 1) (.atom 5) (.atom 6))
      (.cell (.elem 2) (.elem 6)) (.elem 6) = true := by
  native_decide
theorem ite_false_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 6)) (.elem 6) := .elem 6

/-- Allocation and read through the aligned store: the object cell
    lands after the knot prefix and comes back correctly. -/
theorem ref_deref_runs :
    check (.deref (.ref (.atom 6)))
      (.cell (.elem 2) (.elem 6)) (.elem 6) = true := by
  native_decide
theorem ref_deref_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 6)) (.elem 6) := .elem 6

/-- Write through the aligned store (`setref` returns the written
    value). -/
theorem setref_runs :
    check (.app (.lam (.setref (.var 0) (.atom 7))) (.ref (.atom 2)))
      (.cell (.elem 2) (.elem 7)) (.elem 7) = true := by
  native_decide
theorem setref_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 7)) (.elem 7) := .elem 7

/-- Host absorption: the object continuation, invoked inside the
    interpreted world, escapes through META's single host `callcc`
    and delivers the direct value. -/
theorem callcc_throw_runs :
    check (.callcc (.app (.var 0) (.atom 5)))
      (.cell (.elem 2) (.elem 5)) (.elem 5) = true := by
  native_decide
theorem callcc_throw_rep :
    RepV K₀ KRempty (.cell (.elem 2) (.elem 5)) (.elem 5) := .elem 5

end AdequacyInstances
end Dichotomic

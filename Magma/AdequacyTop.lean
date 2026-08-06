import Magma.AdequacyControl

/-!
# Adequacy campaign, rung 7: the top theorem

The target theorem of ADEQUACY.md §0, in its stated form — and with
it the campaign closes.

* **`interpreter_adequacy`** — for every program of the 13-form
  domain there is a **monotone fuel transformer** `F`: whenever the
  direct run converges within `n` steps, META's run converges
  within `F n` steps to a representing value; and if the direct run
  diverges, META's run diverges. Uniformity in fuel, as demanded:
  convergence and divergence transfer together.
* **`halts_iff`** — the crispest consequence: **the interpreted
  program halts if and only if the program halts**. Interpretation
  is termination-transparent.
* **`observable_agreement`** — for observable (element) results the
  interpreter's answer is *determined*: if `p` runs to `elem k`,
  META's run produces exactly the tagged `(quo . k)` — not merely a
  related value; the representation relation pins element results
  uniquely.
* **`law_lift`** — corollary 2 of the plan, packaged: any
  element-observable equation between programs certified at the
  machine holds verbatim between their interpretations. The
  certified laws — β, the factorization law, store discipline —
  lift to the interpreted world with no new proofs, because
  machine-equal programs are interpreted-equal.

Corollary 3 (the 17-program corpus demotes from evidence to
regression test) is discharged by existence: every corpus behavior
is an instance of `interpreter_adequacy`; the Rust difftest keeps
the corpus as cross-implementation regression armor, which is all
it still needs to be.

With rung 6's `tower` (collapse at every height) and this file, all
four corollaries of §0 are theorems. The statement mentions one
machine and nothing else.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyTop

open FactorizationEqv MetaImage AdequacyStartup AdequacyRep AdequacyControl

/-- **The top theorem** (ADEQUACY.md §0): a monotone fuel
    transformer under which META's run tracks the direct run —
    convergence within `n` direct steps becomes convergence within
    `F n` META steps to a representing value, and divergence
    transfers. -/
theorem interpreter_adequacy (p : Prog) (hp : EqvFree p) :
    ∃ F : Nat → Nat, Monotone F ∧
      (∀ (n : Nat) (v : Val), runM n [] [] p = some v →
        ∃ vT, RepVc [quoteD p] vT v ∧
          loop (F n) (metaState p) = some vT) ∧
      ((∀ n, runM n [] [] p = none) →
        ∀ m, loop m (metaState p) = none) := by
  have hch : ∀ n : Nat, ∃ m : Nat, ∀ v : Val,
      runM n [] [] p = some v →
      ∃ vT, RepVc [quoteD p] vT v ∧ loop m (metaState p) = some vT := by
    intro n
    cases hr : runM n [] [] p with
    | none => exact ⟨0, fun v hv => absurd hv (by simp)⟩
    | some v =>
      obtain ⟨m, vT, rep, hm⟩ := adequacy_ctl hp hr
      refine ⟨m, fun v' hv' => ?_⟩
      cases hv'
      exact ⟨vT, rep, hm⟩
  choose F0 hF0 using hch
  refine ⟨fun n => Nat.rec (motive := fun _ => Nat) (F0 0)
    (fun k acc => max acc (F0 (k + 1))) n, ?_, ?_, ?_⟩
  · exact monotone_nat_of_le_succ fun n => le_max_left _ _
  · intro n v hv
    have hle : F0 n ≤ Nat.rec (motive := fun _ => Nat) (F0 0)
        (fun k acc => max acc (F0 (k + 1))) n := by
      cases n with
      | zero => exact Nat.le_refl _
      | succ k => exact le_max_right _ _
    obtain ⟨vT, rep, hm⟩ := hF0 n v hv
    exact ⟨vT, rep, loop_mono_le hle hm⟩
  · exact meta_diverges hp

/-- **Interpretation is termination-transparent**: the interpreted
    program halts iff the program halts. -/
theorem halts_iff (p : Prog) (hp : EqvFree p) :
    (∃ n v, runM n [] [] p = some v) ↔
    (∃ m vT, loop m (metaState p) = some vT) := by
  constructor
  · rintro ⟨n, v, h⟩
    obtain ⟨m, vT, _, hm⟩ := adequacy_ctl hp h
    exact ⟨m, vT, hm⟩
  · rintro ⟨m, vT, hm⟩
    by_contra hno
    push_neg at hno
    have hdiv : ∀ n, runM n [] [] p = none := by
      intro n
      cases hr : runM n [] [] p with
      | none => rfl
      | some v => exact absurd hr (hno n v)
    rw [meta_diverges hp hdiv m] at hm
    exact absurd hm (by simp)

/-- **Observable results are determined**: if the direct run
    produces an element, META's run produces exactly its tagged
    quotation — the relation pins element results uniquely. -/
theorem observable_agreement (p : Prog) (hp : EqvFree p) {n : Nat}
    {k : Fin 8} (h : runM n [] [] p = some (.elem k)) :
    ∃ m, loop m (metaState p) = some (.cell (.elem 2) (.elem k)) := by
  obtain ⟨m, vT, rep, hm⟩ := adequacy_ctl hp h
  obtain rfl := elemRc rep
  exact ⟨m, hm⟩

/-- **Certified laws lift** (corollary 2 of the plan): any
    element-observable equation between programs proven at the
    machine holds verbatim between their interpretations — β, the
    factorization law, store discipline, all of it, with no new
    proofs. -/
theorem law_lift {p q : Prog} (hp : EqvFree p) (hq : EqvFree q)
    {k : Fin 8} {n₁ n₂ : Nat}
    (h₁ : runM n₁ [] [] p = some (.elem k))
    (h₂ : runM n₂ [] [] q = some (.elem k)) :
    ∃ m₁ m₂,
      loop m₁ (metaState p) = some (.cell (.elem 2) (.elem k)) ∧
      loop m₂ (metaState q) = some (.cell (.elem 2) (.elem k)) := by
  obtain ⟨m₁, hm₁⟩ := observable_agreement p hp h₁
  obtain ⟨m₂, hm₂⟩ := observable_agreement q hq h₂
  exact ⟨m₁, m₂, hm₁, hm₂⟩

end AdequacyTop
end Dichotomic

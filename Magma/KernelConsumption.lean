import Magma.AdequacySim
import Magma.Homoiconic

/-!
# The consumption lemmas: META's atom case spends S, D, and C — one law each

The 2026-08-14 ICP investigation found that the abstract ICP theorem
(`artifactA8_icp_through_quote`) was a leaf of the dependency DAG —
referenced by nothing — while row 6's actual content was silently
load-bearing inside the frozen META image: the atom branch of `meval`
(`MetaImage.lean`, the group forwarded through `v23`) is the three-probe
program

    if minn x               -- probe 1: mnot (data? ⬝ x)     … capability D
    then eval ⬝ x           -- payoff: row 3                  … capability S
    else if mnot (judge? ⬝ x) -- probe 2: row 6, one lookup   … capability C
    then eval ⬝ x
    else x                  -- absorbers are self-representing

This file names that dependency. `leafSpec` transcribes the branch at
table level; the probe lemmas certify what each probe consumes:

* **D at probe 1** (`probe1_consumes_introspection`, proved *from*
  `artifactA8_introspection` + `artifactA8_has_dichotomy`): `minn`
  reads the sort partition through one `data?` application; surface
  form `probe1_reads_sort`.
* **C at probe 2** (`probe2_is_icp`, proved *from*
  `artifactA8_icp_through_quote`): row 6's answer is the composite
  `data? ∘ quote` fused into one Cayley lookup — and `probe2_forced`
  shows no other row could serve: row 6 is the unique element whose
  row separates the code block {5,6,7} from the absorbers through
  machine truthiness. In particular `data?` itself cannot.
* **S at the payoff** (`leafSpec_qatom`, proved *from* `eatom_qatom`):
  the branch returns `eval ⬝ x`, and its correctness on quotations is
  exactly the retraction law.

`meval_atom_runs_leafSpec` closes the bridge: META's certified atom
reduction (`meval_atom`, rung 3b) returns precisely the tagged
`leafSpec` answer, so `interpreter_adequacy`'s base case decomposes
into the three certified laws — the atom case of the self-interpreter
consumes exactly S, D, and C, one instruction each. The step-count
fingerprint agrees: judges exit at probe 1 (48 steps), operators fall
through to probe 2 (70), absorbers fail both probes and skip the
payoff application (66) — `atomSteps` in `AdequacySim.lean`.

Finally, the witness classifications (`artifactA8_icp_witnesses`,
`kernel6_icp_witnesses`) repair a prose overclaim: "the single internal
composition" (paper §5.2) is not unique as a *triple* — but every ICP
witness in both the N=6 kernel and the artifact is an instance of the
homoiconicity law: one sort classifier factoring through the
complementary classifier along a block-swapping operator. The
composition capability, wherever it is realized, is code recognition.
-/

set_option autoImplicit false

namespace Dichotomic
namespace KernelConsumption

open Factorization (qatom eatom eatom_qatom)
open FactorizationEqv AdequacyStartup AdequacySim MetaTags

-- ═══════════════════════════════════════════════════════════════════
-- The leaf spec: META's atom branch, transcribed at table level
-- ═══════════════════════════════════════════════════════════════════

/-- META's atom branch as a table-level function: probe 1 is `minn`
    (one `data?` application), probe 2 is `mnot (judge? ⬝ x)` (one
    row-6 application), the payoff is one `eval` application, and the
    fall-through returns the atom unchanged. Transcribed arm for arm
    from the `v23` group of the frozen image (`MetaImage.META`). -/
def leafSpec (x : Fin 8) : Fin 8 :=
  if minn x then dotA8 3 x
  else if !truthy (dotA8 6 x) then dotA8 3 x
  else x

-- ═══════════════════════════════════════════════════════════════════
-- What each probe consumes
-- ═══════════════════════════════════════════════════════════════════

/-- **D consumed at probe 1, at the proof-term level**: on core, `minn`
    answers `true` exactly on the non-classifier (operator) side of the
    sort partition — proved *from* the introspection law
    (`artifactA8_introspection`, spent in both directions) and the
    dichotomy (`artifactA8_has_dichotomy`, spent in the forward
    direction to know the sides are exhaustive), the way
    `probe2_is_icp` spends the ICP law and `leafSpec_qatom` spends the
    retraction. -/
theorem probe1_consumes_introspection :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      (minn x = true ↔ NclSide 8 dotA8 0 1 x) := by
  intro x h0 h1
  have hIntro := artifactA8_introspection x h0 h1
  constructor
  · intro hm
    rcases artifactA8_has_dichotomy.2.1 x with hz0 | hz1 | hc | hn
    · exact absurd hz0 h0
    · exact absurd hz1 h1
    · exfalso
      have h5 : dotA8 5 x = 0 := hIntro.1 hc
      simp [minn, truthy, h5] at hm
    · exact hn
  · intro hn
    have h5 : dotA8 5 x = 1 := hIntro.2 hn
    simp [minn, truthy, h5]

/-- The surface form of probe 1: the artifact's non-classifier side is
    exactly the operator block `{2,3,4}` (the sort census, `decide`),
    so `minn` accepts exactly the operators
    (`MetaTags.minn_iff_operator`; law-consuming form above). -/
theorem probe1_reads_sort :
    ∀ x : Fin 8, minn x = true ↔ (x = 2 ∨ x = 3 ∨ x = 4) :=
  minn_iff_operator

/-- **C consumed at probe 2**: row 6's answer is the ICP composite —
    `judge? ⬝ x = data? ⬝ (quote ⬝ x)` at every column. On the core this
    is the certified ICP law `artifactA8_icp_through_quote`; the two
    absorber columns, which the law does not cover, are checked
    directly. Read operationally: probe 2 is the two-instruction test
    "quote it, then ask `data?`" fused into one Cayley lookup — the
    economy ICP buys the interpreter. -/
theorem probe2_is_icp : ∀ x : Fin 8, dotA8 6 x = dotA8 5 (dotA8 2 x) := by
  intro x
  by_cases h0 : x = 0
  · subst h0; decide
  · by_cases h1 : x = 1
    · subst h1; decide
    · exact artifactA8_icp_through_quote x h0 h1

/-- **Probe 2 is forced**: no row other than 6 separates the code block
    {5,6,7} from the absorbers {0,1} through machine truthiness — for
    every other element some code and some absorber answer alike. In
    particular `data?` itself cannot serve (it answers in the accept
    channel on both), which is why the branch needs a second classifier
    at all. -/
theorem probe2_forced :
    ∀ r : Fin 8, r ≠ 6 →
      ∃ x y : Fin 8, (x = 5 ∨ x = 6 ∨ x = 7) ∧ (y = 0 ∨ y = 1) ∧
        truthy (dotA8 r x) = truthy (dotA8 r y) := by decide

-- ═══════════════════════════════════════════════════════════════════
-- S consumed at the payoff: the branch computes atomic decoding
-- ═══════════════════════════════════════════════════════════════════

/-- The leaf spec computes `eatom` at every column — the two probes
    route each block to the arm where one `eval` application (or
    absorber self-representation) is the correct answer. -/
theorem leafSpec_computes_eatom : ∀ x : Fin 8, leafSpec x = eatom x := by
  decide

/-- **S consumed at the payoff**: on quotations the branch is the
    identity — correctness is exactly the certified retraction law
    `eatom_qatom`, spent here in the proof term. -/
theorem leafSpec_qatom : ∀ a : Fin 8, leafSpec (qatom a) = a := by
  intro a
  rw [leafSpec_computes_eatom]
  exact eatom_qatom a

-- ═══════════════════════════════════════════════════════════════════
-- The bridge: META's certified atom reduction runs the leaf spec
-- ═══════════════════════════════════════════════════════════════════

/-- **The consumption bridge**: META's atom case returns exactly the
    tagged `leafSpec` answer, so the base case of the adequacy
    campaign decomposes into the three certified laws — D at probe 1,
    C at probe 2, S at the payoff. One capability per instruction;
    nothing else of the table is consumed. -/
theorem meval_atom_runs_leafSpec (ρ₀ : Env) (a : Fin 8) (ρT : Val) (κ : Kont) :
    stepIter (atomSteps a) (mevalCall ρ₀ (quoteD (.atom a)) ρT κ) =
      .inl (.ret (.cell (.elem 2) (.elem (leafSpec (qatom a))))
        (knotStoreF ρ₀) κ) := by
  rw [leafSpec_qatom]
  exact meval_atom ρ₀ a ρT κ

-- ═══════════════════════════════════════════════════════════════════
-- Witness classification: every internal composition is code recognition
-- ═══════════════════════════════════════════════════════════════════

/-- The triple form of `HasICP`'s body, specialized to the artifact:
    (a, b, c) witnesses ICP when a ⬝ x = c ⬝ (b ⬝ x) on core with b
    core-preserving and a non-constant on core. -/
@[reducible] def ICPWitnessA8 (a b c : Fin 8) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
  a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧ c ≠ 0 ∧ c ≠ 1 ∧
  (∀ x : Fin 8, x = 0 ∨ x = 1 ∨ (dotA8 b x ≠ 0 ∧ dotA8 b x ≠ 1)) ∧
  (∀ x : Fin 8, x = 0 ∨ x = 1 ∨ dotA8 a x = dotA8 c (dotA8 b x)) ∧
  (∃ x y : Fin 8, x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1 ∧ dotA8 a x ≠ dotA8 a y)

/-- **Every ICP witness in the artifact is a homoiconicity law**: the
    factoring element is a sort classifier, the outer element is the
    complementary classifier, and the inner element is a block-swapping
    operator (quote, eval, or shift). Six triples, all instances of
    complementation-through-quotation; `shift?` participates in none. -/
theorem artifactA8_icp_witnesses :
    ∀ a b c : Fin 8, ICPWitnessA8 a b c ↔
      (((a = 5 ∧ c = 6) ∨ (a = 6 ∧ c = 5)) ∧ (b = 2 ∨ b = 3 ∨ b = 4)) := by
  decide

/-- The triple form of `HasICP`'s body for the N=6 kernel. -/
@[reducible] def ICPWitnessK6 (a b c : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
  a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1 ∧ c ≠ 0 ∧ c ≠ 1 ∧
  (∀ x : Fin 6, x = 0 ∨ x = 1 ∨ (dotK6 b x ≠ 0 ∧ dotK6 b x ≠ 1)) ∧
  (∀ x : Fin 6, x = 0 ∨ x = 1 ∨ dotK6 a x = dotK6 c (dotK6 b x)) ∧
  (∃ x y : Fin 6, x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1 ∧ dotK6 a x ≠ dotK6 a y)

/-- **Every ICP witness in the N=6 kernel is a homoiconicity law**: a
    classifier factoring through the complementary classifier along
    quote or eval. Four triples — so "the single internal composition"
    is not literally a unique triple, but every realization of C in the
    kernel is the same law: code recognition by complementation through
    quotation. -/
theorem kernel6_icp_witnesses :
    ∀ a b c : Fin 6, ICPWitnessK6 a b c ↔
      (((a = 4 ∧ c = 5) ∨ (a = 5 ∧ c = 4)) ∧ (b = 2 ∨ b = 3)) := by
  decide

end KernelConsumption
end Dichotomic

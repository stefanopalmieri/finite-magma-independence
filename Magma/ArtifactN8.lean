import Magma.Dichotomic
import Magma.ICP
import Magma.E2PM
import Magma.Sorting
import Magma.Homoiconic

/-!
# The Canonical N=8 Artifact (Stack A): a Certified Scheme Microcode

The R7RS-directed instruction table: the homoiconic kernel plus one free
dual pair, closed under the full law set

  * kernel: swap world, quote/eval retraction, sort-introspection,
    `judge? = data? ∘ quote`;
  * the free operator (shift) is **faithful** (injective on core);
  * **hygiene**: shift commutes with quote and with eval, and is an
    involution;
  * shift acts differently from quote and from eval;
  * judge-closure under quote.

SAT enumeration shows this law set — including the no-internal-dispatch
law adopted 2026-08-01 (`scripts/canonicality/probe_dispatch.py`) —
admits exactly **168** distinct core
tables at N=8; the artifact below is the canonical one — the
lexicographically minimal table, extracted by greedy minimization, so it
is *derived*, not designed (`scripts/n8_free_pair_search.py`).

```
     0  1  2  3  4  5  6  7
  0 [0, 0, 0, 0, 0, 0, 0, 0]   ← halt-true  (absorber)
  1 [1, 1, 1, 1, 1, 1, 1, 1]   ← halt-false (absorber)
  2 [0, 0, 5, 6, 7, 2, 3, 4]   ← QUOTE (s): the involution i ↔ i+3
  3 [0, 1, 5, 6, 7, 2, 3, 4]   ← EVAL  (r): same core action (self-inverse
                                   quotation), marked at the halt-false column
  4 [0, 0, 5, 7, 6, 2, 4, 3]   ← SHIFT (γ): faithful hygiene operator
  5 [0, 0, 1, 1, 1, 0, 0, 0]   ← data?  (κ): sort introspection
  6 [0, 0, 0, 0, 0, 1, 1, 1]   ← judge?     : data? ∘ quote
  7 [0, 0, 0, 0, 1, 0, 0, 1]   ← shift?     : emergent (see below)
```

Emergent structure (present in the canonical table without being asked
for by any law):

* **The duality pairing is the ISA's own documentation**: each
  operator's code is its judge — `quote⬝quote = data?`,
  `quote⬝eval = judge?`, `quote⬝shift = shift?`
  (`artifactA8_duality_pairing`).
* **The free judge slot resolved itself into `shift?`**: it accepts
  exactly shift and shift's code (`artifactA8_shift_recognizer`).
* **Quotation is an involution** here — the lex-min table chose
  self-inverse quotation, making eval agree with quote on the core and
  differ only by one marker bit (`artifactA8_quote_involution`).

The driver loop (external, per K-infinity) supplies iteration, the tape
supplies pairs/vectors/numbers (per the pairing and recognizer walls),
and R7RS's user-facing `quote`/`eval` are driver-level operations over
tape representations, underwritten by this table's internal duality.
-/

set_option autoImplicit false

namespace Dichotomic

private def rawA8 : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0 | 0, 4 => 0 | 0, 5 => 0 | 0, 6 => 0 | 0, 7 => 0
  | 1, 0 => 1 | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1 | 1, 6 => 1 | 1, 7 => 1
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 5 | 2, 3 => 6 | 2, 4 => 7 | 2, 5 => 2 | 2, 6 => 3 | 2, 7 => 4
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 5 | 3, 3 => 6 | 3, 4 => 7 | 3, 5 => 2 | 3, 6 => 3 | 3, 7 => 4
  | 4, 0 => 0 | 4, 1 => 0 | 4, 2 => 5 | 4, 3 => 7 | 4, 4 => 6 | 4, 5 => 2 | 4, 6 => 4 | 4, 7 => 3
  | 5, 0 => 0 | 5, 1 => 0 | 5, 2 => 1 | 5, 3 => 1 | 5, 4 => 1 | 5, 5 => 0 | 5, 6 => 0 | 5, 7 => 0
  | 6, 0 => 0 | 6, 1 => 0 | 6, 2 => 0 | 6, 3 => 0 | 6, 4 => 0 | 6, 5 => 1 | 6, 6 => 1 | 6, 7 => 1
  | 7, 0 => 0 | 7, 1 => 0 | 7, 2 => 0 | 7, 3 => 0 | 7, 4 => 1 | 7, 5 => 0 | 7, 6 => 0 | 7, 7 => 1
  | _, _ => 0

private theorem rawA8_bound (a b : Fin 8) : rawA8 a.val b.val < 8 := by
  revert a b; decide

def dotA8 (a b : Fin 8) : Fin 8 := ⟨rawA8 a.val b.val, rawA8_bound a b⟩

/-- The artifact is a full FaithfulRetractMagma (quote = 2, eval = 3). -/
def artifactA8_frm : FaithfulRetractMagma 8 where
  dot := dotA8
  zero₁ := 0
  zero₂ := 1
  sec := 2
  ret := 3
  zero₁_left := by decide
  zero₂_left := by decide
  zeros_distinct := by decide
  no_other_zeros := by decide
  extensional := by decide
  ret_sec := by decide
  sec_ret := by decide
  ret_zero₁ := by decide

theorem artifactA8_has_retract : HasRetractPair 8 dotA8 0 1 := by decide
theorem artifactA8_has_dichotomy : HasDichotomy 8 dotA8 0 1 := by decide
theorem artifactA8_has_icp : HasICP 8 dotA8 0 1 := by decide
theorem artifactA8_sorted : Sorted 8 dotA8 0 1 := by decide
theorem artifactA8_swapping : ClassSwapping 8 dotA8 0 1 := by decide

/-- `data?` (element 5) internally decides the sort partition. -/
theorem artifactA8_introspection : SortIntrospection 8 dotA8 0 1 5 := by decide

/-- The forced negation law: `data?` answers oppositely on x and (quote x). -/
theorem artifactA8_negation :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 5 (dotA8 2 x) ≠ dotA8 5 x := by decide

/-- The homoiconicity ICP: `judge? = data? ∘ quote` on the core. -/
theorem artifactA8_icp_through_quote :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 6 x = dotA8 5 (dotA8 2 x) := by decide

/-- Hygiene 1: shift commutes with quote on the core. -/
theorem artifactA8_shift_quote_comm :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 4 (dotA8 2 x) = dotA8 2 (dotA8 4 x) := by decide

/-- Hygiene 2: shift commutes with eval on the core. -/
theorem artifactA8_shift_eval_comm :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 4 (dotA8 3 x) = dotA8 3 (dotA8 4 x) := by decide

/-- Hygiene 3: shift is an involution on the core. -/
theorem artifactA8_shift_involution :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 4 (dotA8 4 x) = x := by decide

/-- Hygiene 4: shift is faithful (injective on the core). -/
theorem artifactA8_shift_faithful :
    ∀ x y : Fin 8, x ≠ 0 → x ≠ 1 → y ≠ 0 → y ≠ 1 →
      dotA8 4 x = dotA8 4 y → x = y := by decide

/-- Quotation is an involution in the canonical artifact: `quote² = id`
    on the core (self-inverse quotation; eval agrees with quote on core). -/
theorem artifactA8_quote_involution :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 2 (dotA8 2 x) = x := by decide

/-- **The duality pairing documents the ISA**: each operator's code is
    its judge — quote ↦ `data?`, eval ↦ `judge?`, shift ↦ `shift?`. -/
theorem artifactA8_duality_pairing :
    dotA8 2 2 = 5 ∧ dotA8 2 3 = 6 ∧ dotA8 2 4 = 7 := by decide

/-- Emergent: the free judge is `shift?` — it accepts exactly shift and
    shift's code, and nothing else on the core. -/
theorem artifactA8_shift_recognizer :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      (dotA8 7 x = 1 ↔ (x = 4 ∨ x = 7)) := by decide

/-- **The canonical N=8 artifact**: eight instructions — halt-true,
    halt-false, quote, eval, shift, `data?`, `judge?`, `shift?` —
    carrying S, D, C, the sorted swap world, introspection, and the
    hygiene laws; the lexicographically minimal member of the 168-table
    design space determined by the full law set. -/
theorem canonical_artifact_N8 :
    ∃ (_ : FaithfulRetractMagma 8),
      HasRetractPair 8 dotA8 0 1 ∧ HasDichotomy 8 dotA8 0 1 ∧
      HasICP 8 dotA8 0 1 ∧ Sorted 8 dotA8 0 1 ∧
      ClassSwapping 8 dotA8 0 1 ∧ SortIntrospection 8 dotA8 0 1 5 :=
  ⟨artifactA8_frm, artifactA8_has_retract, artifactA8_has_dichotomy,
    artifactA8_has_icp, artifactA8_sorted, artifactA8_swapping,
    artifactA8_introspection⟩

end Dichotomic

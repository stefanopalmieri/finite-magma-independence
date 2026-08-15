import Magma.ArtifactN8

/-!
# The parity grading of the core actions (N = 8)

The left-regular core actions of the canonical artifact's operator
rows generate a Klein four-group inside the symmetric group on the
core, graded by *block parity* — does the action exchange the
operator block `{2,3,4}` with the judge block `{5,6,7}`, or preserve
the blocks? The grading is the two-level architecture in miniature:

* **Odd (level-crossing) — the instructions.** Quote and eval share
  one core action, `q = (2 5)(3 6)(4 7)`
  (`eval_action_eq_quote_action`); shift acts as
  `γ = (2 5)(3 7)(4 6)`. Both are involutions
  (`artifactA8_quote_involution`, `artifactA8_shift_involution`),
  they commute (`quote_shift_actions_commute`), and every operator
  row swaps the blocks (the sorting law, `artifactA8_swapping`) — to
  be an instruction in this algebra is to cross the use/mention
  boundary.
* **Even (level-preserving) — driver-side only.** The product
  `qγ` is the cycle-swap `(3 4)(6 7)` (`quote_shift_is_cycleSwap`),
  the renaming that exchanges eval's quote-cycle with shift's while
  fixing quote's. Neither it nor the identity is realized by any row
  (`no_row_realizes_id`, `no_row_realizes_cycleSwap`) — **there is no
  internal no-op**, and the swap-world quote²-exclusion, previously a
  SAT record, is here a kernel-checked theorem at N = 8.
* **The tariff.** Every even element is computable in exactly two
  Cayley lookups and provably never in one: the identity as quote
  twice (`artifactA8_quote_involution` — or anchored,
  `eatom_qatom`), the cycle-swap as quote-after-shift
  (`quote_shift_is_cycleSwap`). Internality = odd parity = cost 1;
  derived = even parity = cost 2; there is no cost-3 tier. Rung 0's
  retraction law `eval ∘ quote = id` is the algebra buying back its
  own forbidden no-op at the minimum price the walls allow.
* **One quotation up to bookkeeping.** Shift is quote twisted by the
  cycle-swap (`shift_action_eq_quote_after_cycleSwap`): the odd coset
  is a single orbit under the even subgroup, so instruction diversity
  is level-preserving relabeling applied to a single reflective
  primitive.

At N = 6 the same grading lives in a different container: quote has
core order 4 there (`kernel6_quote_order_four`), so the closure is
`ℤ/4` with even part `{id, quote²}` — the group varies with the
model, the parity does not (`swap_even_order`, `QuoteOrbit.lean`).
The artifact itself has *no* symmetries (`autA8_trivial`): the Klein
group is not an automorphism group, it is the closure of what the
instructions do. Diagram: `docs/parity-grading.png`.
-/

set_option autoImplicit false

namespace Dichotomic
namespace ParityN8

/-- The cycle-swap `(3 4)(6 7)`: the even, level-preserving renaming
    that exchanges eval's quote-cycle `{3,6}` with shift's `{4,7}`
    and fixes quote's `{2,5}`. -/
def cycleSwap : Fin 8 → Fin 8 := fun x =>
  if x = 3 then 4 else if x = 4 then 3
  else if x = 6 then 7 else if x = 7 then 6 else x

/-- Quote and eval have the same core action: rows 2 and 3 differ only
    at the absorber column (eval's marker). One `q`, realized twice. -/
theorem eval_action_eq_quote_action :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 3 x = dotA8 2 x := by decide

/-- The quote and shift core actions commute — the closure of the
    realized actions is abelian. -/
theorem quote_shift_actions_commute :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      dotA8 2 (dotA8 4 x) = dotA8 4 (dotA8 2 x) := by decide

/-- The product of the two realized actions is the cycle-swap:
    `q ∘ γ = (3 4)(6 7)` on core. With the two involution laws and
    commutativity, the closure `{id, q, γ, qγ}` is a Klein four-group. -/
theorem quote_shift_is_cycleSwap :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      dotA8 2 (dotA8 4 x) = cycleSwap x := by decide

/-- **One quotation up to bookkeeping**: shift's core action is
    quote's composed with the cycle-swap — the odd coset is a single
    orbit under the even subgroup. -/
theorem shift_action_eq_quote_after_cycleSwap :
    ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      dotA8 4 x = dotA8 2 (cycleSwap x) := by decide

/-- **There is no internal no-op**: no row of the table acts as the
    identity on the core. The trivial action is even, and even
    actions are not instructions. -/
theorem no_row_realizes_id :
    ¬ ∃ r : Fin 8, ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 r x = x := by
  decide

/-- **The cycle-swap is driver-side only**: no row realizes it — a
    renaming that does not quote is not an instruction, though the
    driver computes it in two lookups (`quote_shift_is_cycleSwap`). -/
theorem no_row_realizes_cycleSwap :
    ¬ ∃ r : Fin 8, ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      dotA8 r x = cycleSwap x := by decide

/-- **The parity grading, packaged**: quote and eval share one action;
    the product of the realized actions is the cycle-swap; and neither
    even element — the identity, the cycle-swap — is realized by any
    row. Odd = instruction = cost one; even = derived = cost two. -/
theorem parity_grading :
    (∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 3 x = dotA8 2 x) ∧
    (∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 2 (dotA8 4 x) = cycleSwap x) ∧
    (¬ ∃ r : Fin 8, ∀ x : Fin 8, x ≠ 0 → x ≠ 1 → dotA8 r x = x) ∧
    (¬ ∃ r : Fin 8, ∀ x : Fin 8, x ≠ 0 → x ≠ 1 →
      dotA8 r x = cycleSwap x) :=
  ⟨eval_action_eq_quote_action, quote_shift_is_cycleSwap,
   no_row_realizes_id, no_row_realizes_cycleSwap⟩

end ParityN8
end Dichotomic

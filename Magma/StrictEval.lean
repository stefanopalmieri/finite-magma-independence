import Magma.ErrorRequests
import Magma.AdequacyTop

/-!
# Strict Eval Meets Adequacy: Judging at the Boundary

The closing glue of the error-payload design. Adequacy makes META
*provably blind* to error observation: the interpreter implements the
machine's fail-open defaults in-band (its dispatch is total, so no
machine error transition ever fires during interpretation), and that
blindness is META being *correct*. So the strict verdict for
untrusted quoted code belongs at the decode boundary — strict eval =
decode + the strict machine (`ErrorRequests.evalE`) — and nothing is
lost by never probing through the interpreter:

**`strict_eval_meta`**: if strict eval accepts `⌜p⌝` with value `v`,
then META interpreting `⌜p⌝` converges to a value representing `v`.
Judge the direct run; adequacy transfers the verdict to every
interpretation. One composition — `strict_iff` (the verdict is a
clean certified run) through `loopT_fst` (erasure) into
`interpreter_adequacy` (the run transfers to META) — and no theorem
had to change to make the pieces meet.
-/

set_option autoImplicit false

namespace Dichotomic
namespace StrictEval

open FactorizationEqv ErrorRequests AdequacyStartup AdequacyRep
  AdequacyControl AdequacyTop

/-- **Strict acceptance transfers to META**: if strict eval accepts
    the quotation of an `EqvFree` program with value `v`, then META
    interpreting that quotation converges to a `RepVc`-representative
    of `v`. The judge works at the boundary; the tower inherits the
    verdict. -/
theorem strict_eval_meta (p : Prog) (hp : EqvFree p) (fuel : Nat)
    (v : Val) (h : evalE fuel [] [] (quoteD p) = some (.inl v)) :
    ∃ vT m, RepVc [quoteD p] vT v ∧ loop m (metaState p) = some vT := by
  have hrun : runM fuel [] [] p = some v := by
    have hd := decode_quote p
    unfold evalE at h
    rw [hd] at h
    have hT := (strict_iff fuel (.eval p [] [] .halt) v).mp h
    have herase := loopT_fst fuel (.eval p [] [] .halt) []
    rw [hT] at herase
    exact herase.symm
  obtain ⟨F, -, hconv, -⟩ := interpreter_adequacy p hp
  obtain ⟨vT, hrep, hloop⟩ := hconv fuel v hrun
  exact ⟨vT, F fuel, hrep, hloop⟩

end StrictEval
end Dichotomic

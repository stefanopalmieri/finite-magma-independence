# N=9 Substrate Archive

The N=9 "canonical-witness Lisp substrate" exploration (2026, pre-dating the
sorted-magma results). Archived, not deleted: this is the empirical trail
that led to several later theorems, and it contains one idea not yet
absorbed into the framework.

## What this was

A 9-element S+D+C magma (`CANONICAL_LISP_N9.md`) with a partial duality
σ = (f η)(Q E) pairing quote↔eval and car↔cdr while σ-fixing cons, cond,
and the tester — plus Ψ-Lisp and Ψ* implementations over it and a zoo of
σ-image experiments.

## Why it is superseded

The swap-balance theorem (`Magma/Sorting.lean`, `swap_balance`) proves a
full class-swapping duality requires |judges| = |operators|, hence an even
core. N=9 has core 7 (odd): **every duality at N=9 is necessarily partial**
— which is why σ kept being forced to fix elements. The friction this
exploration kept hitting was a parity theorem it did not yet have. The
derived replacement path is the N=6 homoiconic kernel
(`Magma/Homoiconic.lean`) and the canonical N=8 Stack-A artifact
(`Magma/ArtifactN8.lean`), even-core, law-determined, Lean-certified.

## What was NOT archived (and why)

The λ̄μμ̃ machine prototype built on this substrate stays live in
`scripts/`: `psi_lambda_mu_n9.py`, `psi_lambda_mu_n9_v2.py`,
`n9_church_2a.py`, `LAMBDA_MU_ON_N9.md`, `RESULT_2A.md`. It is the seed of
the driver decided in `MACHINE.md` (CBV System L / CESK): a working
Curien–Herbelin machine with the polarity involution correctly implemented
(σ-fixed cut trigger; position-swap τ⟨v|e⟩ = ⟨τe|τv⟩) and a 25/25
σ̂-commutation test suite. Port it to sit over `dotA8`; the substrate
dependence is thin.

## Salvage item: σ-internalization

`CANONICAL_LISP_N9.md`'s headline property — a non-trivial automorphism
σ ∈ Aut(M) realized internally by left-multiplication by an element — is a
connecting-axiom candidate the sorted/homoiconic ladder has not absorbed:
sorting internalized the sort *partition*, introspection the sort
*predicate*; σ-internalization would internalize a *symmetry as a row*.
It plugs into the mirror-row/rigidity thread and should be studied against
the N=8 artifact before being reinvented.

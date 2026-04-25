# Categorical canonicality: empirical translation test

This is the companion to `paper/CATEGORICAL_CANONICALITY_PROPOSAL.md`.
The proposal restates S, D, C as properties of the *row-image partial
monoid* `R(X)` of an E2PM. This file verifies the translation
empirically across 3901 N=5 S+D+C iso classes.

Script: `scripts/row_image_invariants.py`. Data:
`scripts/phase_cartography_N5.json`.

## Result 1: the translation holds on every N=5 S+D+C iso class

For each of the 3901 N=5 S+D+C iso classes:

| Operational axiom | Row-image translation | Agreement |
|---|---|---|
| S (retraction pair) | ∃ a, b ∈ core: λ(b)∘λ(a)\|core = id, λ(a)∘λ(b)\|core = id | 3901/3901 |
| D (classifier dichotomy) | R(X)\|core = R_clas ⊔ R_core, both inhabited, no mixed | 3901/3901 |
| C (ICP) | ∃ a, b, c ∈ core distinct: λ(b) core-preserving, λ(a)\|core = λ(c)∘λ(b)\|core, λ(a) non-constant | 3901/3901 |

Zero disagreements. The row-image categorical reading is consistent with
the operational definitions across the entire N=5 S+D+C population.

This is a translation, not a theorem — but it confirms the row-image
language captures S, D, C without distortion. The same translation
should be checkable at N=6, N=7, etc. (TODO).

## Result 2: the canonical decomposition is forced at N=5

The decomposition `(|R_clas|, |R_core|, |mixed|)` was uniformly
**(2, 1, 0)** across all 3901 classes — *every* core element is either a
classifier or a core-preserving (non-classifier) row, with exactly 2
classifiers and 1 non-classifier. This is exactly the content of
Theorem 4.8(i), now expressed as a structural invariant of `R(X)`.

The categorical reading: at the minimum coexistence size, the row-image
partial monoid has a canonical 3-block decomposition (R_abs of size 2,
R_clas of size 2, R_core of size 1). All 3901 magmas instantiate the
same R-block-structure.

## Result 3: a finer invariant — composition-closure count

The `H_triple_count` from the cartography is uniformly 2 at N=5, but
this counted only *distinct-element* triples (the operational ICP
definition). The row-image perspective suggests counting *all*
composition closures `(a, b, c) ∈ core³` with `λ(c)∘λ(b) = λ(a)` on core
and `λ(b)` core-preserving (without distinctness constraint). This is a
finer invariant of the partial monoid.

| closures | classes |  share |
|---------:|--------:|-------:|
|        2 |    1850 |  47.4% |
|        4 |    1521 |  39.0% |
|        5 |     530 |  13.6% |

So although the operational role-shape is uniform across N=5, the
*partial-monoid closure structure* splits the population into three
sub-classes. Walking through one example (the paper's `dotW5`):

  - `g = 2` is the unique non-classifier, with `λ(g)|core = (2,3,4) = id_core`.
  - With `b = g`, the closures `λ(c) ∘ λ(g) = λ(c)` (since `λ(g) = id`)
    hold trivially for every `c`. This contributes 5 closures:
    `(2,2,2), (3,2,3), (4,2,3), (3,2,4), (4,2,4)`.
  - The 2 distinct-element closures `(4,2,3), (3,2,4)` are the H-triples.

Magmas with `g` *not* identity on core have fewer trivial closures, so
their closure count is smaller (2 or 4 rather than 5). The invariant
distinguishes magmas where the non-classifier acts as identity on core
from magmas where it acts as a non-identity permutation. This is a
real structural distinction — the cartography role-shape didn't see it.

## Result 4: what the partial-monoid view buys us

  1. **It removes the operational hand-waving.** S, D, C are now
     *structural properties of `R(X) ⊆ X^X`* — section-retraction in a
     subset of self-maps, codomain-purity decomposition, partial
     composition closure. No "capability" rhetoric.

  2. **It connects to topos theory in a precise (partial) way.** The
     decomposition `R = R_abs ⊔ R_clas ⊔ R_core` makes `ι(2)` look like
     a *partial subobject classifier*: classifier rows are characteristic
     functions for the subsets they classify. Not every subset of core
     is classifiable (D doesn't claim it is), but at least one is, and
     the rest of the row-image is core-preserving — codomain purity.

  3. **It generates a new invariant.** Composition-closure count goes
     beyond H-triple count and reveals a sub-population structure that
     the role-shape framework missed.

## What this still does not give us

The translation is empirically validated, but the **canonicality theorem**
— "(S, D, C) is the unique triple of universal-property fragments
identifying retract / partial classifier / partial internal hom on
E2PMs, up to natural equivalence" — is still a conjecture, not a
theorem. Making it formal requires:

  1. Specifying the right fragment of universal-property language
     (objects, morphisms, retracts, classifiers, partial homs).
  2. Defining what it means for an operational axiom on E2PMs to
     *witness* a universal-property fragment.
  3. Proving that S, D, C are the unique witnesses of the three named
     fragments, up to natural equivalence.

This is a multi-paper research program, not a one-script verification.
But the current note shifts the discussion from "is (S, D, C) special?"
(unanswerable without a comparison framework) to "do (S, D, C) match
their proposed universal-property analogs as predicted?" (yes,
empirically — across every N=5 S+D+C iso class).

## Next concrete steps

  1. **Run the same translation test at N=6 and N=7** to verify the
     row-image translations remain valid in the multi-shape regime.
  2. **Formalise the partial-monoid view in Lean.** Define `R(X)` as a
     finite subset of `Fin n → Fin n`, prove the decomposition theorem
     and the section-retraction characterization. This sits below the
     existing `Magma/CatKripkeWallMinimal.lean`.
  3. **Investigate the closure-count invariant.** Two natural sub-classes
     of N=5 S+D+C magmas emerge: those where the non-classifier acts as
     identity on core (closure count 5) and those where it doesn't (2 or
     4). Is this distinction stable under absorber-preserving
     isomorphism? What does it correspond to operationally?
  4. **Identify the precise category of partial transformation algebras**
     of which E2PMs are examples. Inverse semigroups, Munn algebras, and
     "block-graded" partial monoids are all candidates. If E2PM ↪
     [recognised partial transformation category], we inherit
     canonicality from the latter.

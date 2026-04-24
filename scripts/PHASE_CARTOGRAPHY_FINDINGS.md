# Phase-Transition Cartography: Findings

Exploratory enumeration of S+D+C magmas up to absorber-preserving
isomorphism at N ∈ {5, 6, 7}, with per-class role-shape features
(|Aut|, core-classifier/non-classifier counts, retraction-pair count,
strong-R availability, H-triple count, full-classifier count).

Scripts: `phase_cartography.py` (enumeration), `phase_analysis.py`
(cross-N summary). Data: `phase_cartography_N{5,6,7}.json`.

## Sample sizes (each a 120–600 s time-budget sample, not full enumerations)

| N | iso classes | rigid fraction | strong-R fraction | wall time |
|---|------------:|---------------:|------------------:|----------:|
| 5 | 3901        | 99.7%          | 0.0%              |     120 s |
| 6 | 2435        | 100.0%         | 6.9%              |     600 s |
| 7 |  663        | 100.0%         | 0.0%              |     600 s |

The N=7 sample is almost certainly biased toward "simple" models;
strong-R magmas exist at N=7 per the paper (`nonrigid_rdh_N7_strongR.json`)
but Z3's model enumeration order surfaced none in the first 663 iso
classes. N=5 and N=6 samples are large enough to be informative.

## Finding 1: N=5 is shape-locked but not fully automorphism-rigid

Every one of the 3901 sampled N=5 magmas has the same role shape:
`cls2_ncl1_Rp1_H2_sR0` — 2 classifiers, 1 non-classifier in core, exactly
1 retraction pair, 2 H-triples, no strong R. This empirically confirms
Theorem 4.8 across a large sample.

But **12 of the 3901 (0.3%) have non-trivial automorphism group** (|Aut|=2).

**Signature of the non-rigid N=5 cases.** All 12 have 2 *full* classifiers
(rows constant on {z₁,z₂} over the full carrier, not just core), and the
two full classifiers have mirror-image rows under a swap of two core
positions. Example (class #864):

    row 2: [0, 0, 1, 0, 0]
    row 3: [0, 0, 0, 1, 0]

Swapping positions 2 ↔ 3 exchanges the two rows; this swap extends to a
Cayley-table automorphism. So the |Aut|=2 at N=5 comes from a
*classifier-swap symmetry* — the two classifiers are interchangeable.

**Cross-tab at N=5:** rigidity × full-classifier count

    (rigid=True,  full_cls=1): 3552
    (rigid=True,  full_cls=2):  337
    (rigid=False, full_cls=2):   12

Having 2 full classifiers is *necessary but not sufficient* for
non-rigidity: only 12/349 ≈ 3.4% of the 2-full-classifier magmas are
non-rigid. The additional constraint is row symmetry.

### Implication for the paper

Theorem 4.9 (role rigidity) claims **the paper's principal witnesses** are
role-rigid — that remains correct. But an unqualified "N=5 S+D+C magmas
are role-rigid" would be false: a small symmetric subpopulation admits a
classifier-swap automorphism. Theorem 4.8 (role-shape lock-in) is the
stronger universal N=5 statement; full automorphism-level rigidity is a
property of most, not all, S+D+C magmas at N=5.

## Finding 2: N=5 → N=6 is a shape-diversity explosion, 1 → 18 shapes

| N | distinct role shapes observed | top-shape share |
|---|------------------------------:|----------------:|
| 5 | 1                             | 100.0%          |
| 6 | 18                            |  39.8%          |
| 7 | 5                             |  51.7%          |

At N=5 the role shape is completely forced. At N=6 it fractures into 18
distinct shapes with the top shape commanding only 40% of the
population. Axes of variation:

- **core classifier count:** 1 (55%), 2 (44%), 3 (0.2%) — the paper's
  Theorem 3.14 classifier-count bound admits |C|=1 at N=6 via the
  |N|≥3 branch, realised here in majority.
- **retraction-pair count:** 1 (93%), 2 (5%), 4 (2%) — multiple
  retraction pairs are now possible.
- **H-triple count:** 1, 2, 3, 4, or 6.
- **strong-R availability:** 6.9% of N=6 magmas admit a retraction pair
  with s ≠ r. Every strong-R N=6 magma in the sample is rigid (|Aut|=1),
  which contradicts the standard "rigidity fails under strong R at N=6"
  framing — the paper's non-rigid witness (`nonrigid_rdh_N6_strongR.json`)
  is a specific example, not the common case.

The paper's canonical N=5 shape `cls2_ncl1_Rp1_H2_sR0` disappears
entirely at N=6 (0 of 2435 classes have it). Every shape at N=6 is new.

## Finding 3: N=6 → N=7 is not another explosion

The N=7 sample of 663 shows only 5 distinct shapes — fewer in absolute
terms than N=6. This is partly an artefact of the smaller sample (Z3's
first 663 model iterations concentrate on simple magmas), but the
*shape density* (shapes per 1000 classes) also drops: N=6 yields 7.4
shapes per 1000, N=7 yields 7.5 per 1000 — roughly equal, not the
monotonic explosion one might expect.

Most striking at N=7: **all 663 sampled classes have exactly 1
retraction pair and no strong R available**. Strong-R magmas exist at
N=7 (per the paper) but are rare enough that Z3's enumeration did not
surface them. The 5 shapes split between two classifier counts:

| Shape                     |   count |
|---------------------------|--------:|
| cls3_ncl2_Rp1_H1_sR0      |     343 |
| cls3_ncl2_Rp1_H4_sR0      |     220 |
| cls3_ncl2_Rp1_H6_sR0      |      50 |
| cls3_ncl2_Rp1_H2_sR0      |      49 |
| cls2_ncl3_Rp1_H2_sR0      |       1 |

The 3-classifier / 2-non-classifier pattern dominates (662/663 = 99.8%).
The |C|=2 / |N|=3 branch of Theorem 3.14 is realised by exactly 1 of 663
classes in this sample.

## Synthesis

The phase transition between N=5 and N=6 is not just "rigidity fails at
N=6" — it is a **shape-diversity explosion**. The role landscape at N=5
is a single point in shape-space; at N=6 it splits into 18 distinct
shapes covering three classifier counts, four retraction-pair counts,
five H-triple counts, and both strong-R regimes. The "phase transition"
language in the paper understates what's happening: the N=5→N=6
transition is less a phase transition (two phases separated by a
boundary) and more a *decomposition* of a single shape into a
heterogeneous multi-shape landscape.

Three open questions suggested by this data:

1. **Does N=5 full-automorphism rigidity have a closed-form characterisation?**
   All 12 non-rigid cases have 2 full classifiers with mirror-image rows.
   Is the biconditional — "non-rigid at N=5 iff 2 full classifiers with
   matching row-permutation pattern" — provable?
2. **Is shape-diversity a monotone-in-N quantity?** N=6 shows 18 shapes
   (2435 classes), N=7 shows 5 (663 classes). The sample at N=7 is too
   small and too biased to tell — but a focused enumeration that
   explicitly constrains strong-R and various classifier counts could
   give a clean comparison.
3. **Is there a canonical "phase-transition" statistic?** Candidates:
   shape entropy, top-shape concentration, Aut-order expectation. A
   statistic that is constant (say, 1) at N=5 and bounded-above at
   N≥6 would formalise the transition into a theorem-ready quantity.

## Reproducing

    python3 scripts/phase_cartography.py 5 --time 120
    python3 scripts/phase_cartography.py 6 --time 600
    python3 scripts/phase_cartography.py 7 --time 600
    python3 scripts/phase_analysis.py

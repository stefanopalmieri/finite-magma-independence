# Closure-count invariant: structural analysis (N=5, N=6)

Companion to `paper/CATEGORICAL_CANONICALITY_FINDINGS.md` Result 3.
Script: `scripts/closure_invariant_analysis.py`. Data:
`scripts/phase_cartography_N{5,6}.json`.

## Q1. Iso-invariance under absorber-preserving permutations: YES

Tested 30 N=5 representatives, conjugating each by all 12 permutations
fixing {0,1} as a set. Closure count was unchanged in every case
(360/360 trials). Verified.

## Q2. cc=5 ⇔ g = id on core; cc∈{2,4} split is not pure

Letting `g` be the unique non-classifier on core (every N=5 class has
exactly one):

| g | core | action | closure count | classes |
|---|------|--------|--------------:|--------:|
| identity (2,3,4) | identity | **5** | 530 |
| (3,2,4), (2,4,3), (4,3,2) | non-id involution | **2 or 4** | 3371 |

`identity-on-core ⇔ cc=5` is fully clean. But every non-identity g
on core at N=5 happens to be an involution (each of the three
non-identity g rows is a transposition fixing one element), so the
proposed "involution vs other permutation" distinction never
materialises. cc∈{2,4} splits *within* each non-id g row pattern:

```
g|core = (3,2,4): 1432  -> cc=4: 710, cc=2: 722
g|core = (2,4,3): 1247  -> cc=4: 545, cc=2: 702
g|core = (4,3,2):  692  -> cc=4: 266, cc=2: 426
g|core = (2,3,4):  530  -> cc=5: 530   (identity)
```

The 4-vs-2 split is **not** determined by g's row alone. Likely it
depends on whether the classifier rows are stable under g's involution.
Did not chase; flagged as open sub-question.

## Q3. N=6 closure-count distribution

Generalised cc (no distinctness; λ(b) core-preserving) over 2435 N=6
sample classes spreads across 14 values:

```
cc:   1   2   3   4   5   6   7   8   9  10  12  14  16  19
 n: 108 600 147 345   1   5   1 244   9   1   1   1   4 968
```

cc strictly refines role-shape: most shapes split. Examples:

  - `cls1_ncl3_Rp1_H4_sR0` (969): cc=8 (1) vs cc=19 (968).
  - `cls2_ncl2_Rp1_H1_sR0` (345): cc∈{1,2,3}.
  - `cls2_ncl2_Rp1_H4_sR0` (147): cc∈{4,8,9,10}.
  - `cls2_ncl2_Rp1_H3_sR0` (98): uniformly cc=3 (one of few pure shapes).

The cc=19 spike comes from `cls1_ncl3` (3 core-preserving rows) where
core-row slices collide. Cross-tab (#core-preserving, #identity-on-core)
→ cc:

```
(1, 0): cc ∈ {2,4,9}                   (  5)
(2, 0): cc ∈ {1,2,3,4,5,8,9,10}        (1081)
(2, 1): cc = 12                        (   1)
(3, 0): cc ∈ {1,2,3,4,6,7,8,19}        (1343)
(3, 1): cc ∈ {14,16}                   (   5)
```

Identity-on-core inflates cc (consistent with the N=5 picture), but the
exact value is not a simple function of these two counts. The invariant
has real discriminating power at N=6.

## Bonus. R(X) partial-monoid types at N=5

Used a Weisfeiler–Lehman refinement on the 5-row partial composition
graph (initial labels by row role + image profile; iteratively refined
by neighbour-label multisets). Got **663 distinct WL signatures**
across 3901 iso classes. Top signatures cover up to 96 classes each;
long tail. WL is one-sided: distinct signatures imply non-isomorphic
partial monoids, but matching signatures don't strictly imply iso. So
663 is a lower bound on the true partial-monoid iso class count. A
nauty-canonicalised count would tighten this — not done.

## Status summary

| Question | Status |
|---|---|
| Q1 iso-invariance | clean — yes, verified on sample |
| Q2 cc=5 ⇔ g=id_core | clean |
| Q2 cc=4 vs cc=2 | unresolved — not a function of g's row alone |
| Q3 N=6 distribution | computed; cc strictly refines role-shape |
| Bonus partial-monoid types | ≥663 distinct (WL); true count not pinned |

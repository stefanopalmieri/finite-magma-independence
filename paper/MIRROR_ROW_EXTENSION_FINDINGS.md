# Mirror-row absorber-fixing beyond N=5: empirical map

The N=5 mirror-row theorem (Thm 4.13) says every Cayley-table
automorphism of an S+D+C magma at N=5 fixes both absorbers. This note
investigates how far the property extends.

## Result 1: it doesn't extend to N=6 in general

A Z3 search (`scripts/n6_absorber_swap_search.py`) finds explicit
absorber-swap automorphisms at N=6 in *both* the strong-S (s ≠ r) and
weak-S (s = r) regimes, in 0.1 s each.

Weak-S example (sR = rR = 4):

```
Row 0: [0, 0, 0, 0, 0, 0]   z₁
Row 1: [1, 1, 1, 1, 1, 1]   z₂
Row 2: [0, 0, 0, 1, 0, 1]   classifier
Row 3: [1, 1, 0, 1, 1, 0]   classifier
Row 4: [0, 1, 2, 3, 5, 4]   non-classifier (sec = ret)
Row 5: [2, 3, 2, 3, 5, 4]   non-classifier
σ = [1, 0, 3, 2, 4, 5]   absorber-swap, classifier-swap, fixes ncl
```

So mirror-row absorber-fixing is genuinely an N=5 phenomenon at the
level of *generic* S+D+C magmas. The N=5 → N=6 transition isn't only
about role-shape diversification — it's also about absorber-symmetry
loss.

Why this works at N=6 but not N=5: the magma above has *two*
non-classifiers (rows 4 and 5). The N=5 mirror-row proof's Lemma B
relied on the unique-non-classifier hypothesis to force `g·g = g`
(only g is σ-fixed in core when σ swaps classifiers). With two
non-classifiers, σ can fix both, and the chain of forced equalities
breaks.

## Result 2: refining to "unique non-classifier" extends partially

Constraining the role-shape to (|classifiers| = N−3, |non-classifiers|
= 1) — single non-classifier in core — recovers absorber-fixing at
some N but not all:

| N | core | k_cls | strong-S | weak-S | any   | comment         |
|---|-----:|------:|----------|--------|-------|-----------------|
| 5 |    3 |     2 | (vacuous) | UNSAT | UNSAT | mirror-row      |
| 6 |    4 |     3 | UNSAT    | UNSAT  | UNSAT | extends         |
| 7 |    5 |     4 | UNSAT    | **SAT** | **SAT** | breaks at weak-S |
| 8 |    6 |     5 | UNSAT    | UNSAT  | UNSAT | extends         |

(`scripts/unique_ncl_absorber_swap_scaling.py`.)

The N=7 weak-S counterexample:

```
Row 0: [0, 0, 0, 0, 0, 0, 0]   z₁
Row 1: [1, 1, 1, 1, 1, 1, 1]   z₂
Row 2: [1, 1, 0, 0, 1, 1, 0]   τ (cls)
Row 3: [1, 1, 0, 0, 1, 0, 1]   τ (cls)
Row 4: [0, 1, 3, 2, 4, 6, 5]   non-classifier g (sec = ret)
Row 5: [0, 0, 1, 0, 0, 1, 1]   τ (cls)
Row 6: [0, 0, 0, 1, 0, 1, 1]   τ (cls)
σ = [1, 0, 5, 6, 4, 3, 2]   (z₁ z₂)(τ_2 τ_5)(τ_3 τ_6) fixes g
```

So even with a unique non-classifier, weak-S allows absorber-swap auts
at N=7.

## Conjecture: the right hypothesis is unique-ncl + strong-S OR small core

Empirical pattern across the cases I tested:

- |C| ≤ 3 and unique ncl ⇒ UNSAT (verified N=5, 6).
- |C| odd and unique ncl ⇒ UNSAT (verified N=6 |C|=3, N=8 |C|=5).
- |C| ≥ 4 and even and unique ncl ⇒ depends on R: strong-S UNSAT,
  weak-S can be SAT (verified N=7 |C|=4).

A clean unified hypothesis-extension of mirror-row, conjectured:

  **At any N, if a S+D+C magma has a unique non-classifier in core
  AND either (a) strong S (s ≠ r) holds, or (b) |classifiers in core|
  is odd, or (c) |classifiers in core| ≤ 3, then no automorphism swaps
  absorbers.**

Verified at N ∈ {5, 6, 7, 8} (N=5 by mirror-row itself, then for the
relevant sub-shapes at N ≥ 6). The N=9 case (|C|=6 even) would test
condition (c) becoming inactive, and is the natural next target.

## Why does the proof break at N=7 weak-S?

The N=5 mirror-row proof's Lemma B uses two facts:
1. `g·g = g` (forced because g is the unique σ-fixed element in core
   when σ swaps classifiers).
2. The C-triple equation `τ₁·x = τ₂·(g·x)` at `x = g` gives
   `τ₁·g = τ₂·g`. Apply σ to derive `σ(τ₁·g) = σ(τ₁)·g`, which must
   equal `τ₁·g` if σ has no fixed classifier and the only "other"
   classifier is τ₂. But σ swaps Z, so the pre-image is z and σ takes
   it to ¬z. Contradiction.

At N=5 |C|=2, `σ(τ₁) = τ₂` is forced (only one other classifier). At
N=7 |C|=4, `σ(τ₁)` can be any of three other classifiers, and the
C-triple equation only constrains the *specific* pair `(τ₁, τ₂)` that
forms a C-triple — not arbitrary classifier pairs.

The N=7 weak-S counterexample exploits this: it uses a double
transposition `(τ_2 τ_5)(τ_3 τ_6)` that respects a *different* pairing
than the C-triple's pairing. The classifier g-values split as
`{τ_2: z₂, τ_3: z₂, τ_5: z₁, τ_6: z₁}`, and σ swaps each {z₂-image} with
a {z₁-image}, mapping `τ·g` to its absorber-swap, consistent with σ on
Z. The C-triple equation forces only that *some* classifier pair has
matching g-values, not that all pairs do.

The strong-S condition (s ≠ r) presumably forces additional structure
that reduces the freedom — empirically it suffices, but I don't have a
clean algebraic argument yet for why.

## Implication for the paper

The mirror-row theorem at N=5 is genuinely sharp. The natural
unique-non-classifier generalisation does not extend cleanly: N=7
weak-S provides a specific counterexample. This isn't a defect of the
theorem; it's a precise structural fact about how the role-shape
constraints at N=5 are stronger than just "single non-classifier." At
N=5 the size and the |C|=2 force everything; at N≥6 the same hypotheses
admit more flexibility.

The conjectured "single ncl + (strong-S or |C| ≤ 3 or |C| odd)" extension
is a candidate next theorem. The proof would need:
- The cycle parity argument (rules out odd |C| via fixed-classifier
  Lemma A).
- An additional argument for the strong-S case, leveraging s ≠ r to
  force compatible classifier g-values.

## Reproducing

```
python3 scripts/n6_absorber_swap_search.py
python3 scripts/n6_unique_ncl_absorber_swap.py
python3 scripts/unique_ncl_absorber_swap_scaling.py
```

Output: three JSONs in `scripts/` recording examples and SAT/UNSAT
status.

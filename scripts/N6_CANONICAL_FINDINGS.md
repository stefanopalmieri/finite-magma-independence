# N=6 canonical witness: empirical findings

Companion to `scripts/n6_self_symmetric_search.py` and
`scripts/n6_joint_canonical_search.py`. Investigates whether the N=5
canonical-witness principles extend to N=6.

## Two principles, restated

The N=5 canonical witness (paper Remark 4.X) is selected by:

  **P1** (indicator classifiers): each classifier τ in core is the
  characteristic function of `{τ, z₂}`: τ(x) = z₂ iff x ∈ {τ, z₂},
  else z₁. Forces τ to fix both absorbers (τ(zᵢ) = zᵢ) and
  self-recognise (τ(τ) = z₂).

  **P2** (self-symmetric / automorphism-internalising): there exist a
  non-trivial automorphism σ ∈ Aut(M) and an element ρ ∈ M such that
  σ(x) = ρ · x for all x in core. The magma's symmetry is realised by
  left-multiplication by some element.

At N=5 these come bundled — the unique joint canonical witness is the
indicator magma where g (the non-classifier) implements the
classifier-swap. At N=6 the question is more interesting because |core|
= 4, multiple shapes are admissible, and the two principles can
separate.

## Result 1: P2 alone generalises to N=6 in all three R-regimes

`n6_self_symmetric_search.py` finds three explicit self-symmetric N=6
S+D+C magmas (one each for any-S, strong-S, weak-S) in 0.15 s each.
Common pattern across all three:

  - σ has order 2 with |Aut| = 2.
  - σ fixes both absorbers (consistent with the absorber-fixing
    structure mirror-row identifies, even though mirror-row itself is
    N=5-specific).
  - ρ is a non-classifier.
  - **ρ is itself moved by σ** — the element implementing the
    symmetry is one of the elements σ permutes. Self-reference: ρ
    realises σ, σ moves ρ.

Different role-shapes hosted P2 across the three examples:
(cls=2, ncl=2) ×2 and (cls=1, ncl=3) ×1. So P2 doesn't pin a unique
shape at N=6; it spans several.

## Result 2: P1 alone fails on those P2-witnesses

None of the three P2-witnesses satisfies the indicator principle. The
classifiers in those examples don't fix the absorbers (e.g. example
A has τ=4 with `T[4][0] = 1`, mapping z₁ to z₂). So P1 and P2
separate at N=6 in the sense that P2-witnesses Z3 finds aren't
P1-style by accident.

## Result 3: P1 ∧ P2 jointly generalises — the joint canonical witness exists at N=6

`n6_joint_canonical_search.py` searches for an N=6 S+D+C magma
satisfying BOTH principles simultaneously. SAT in all three R-regimes,
0.11–0.12 s each. The strong-S example is particularly clean:

```
       z₁  z₂  τ₁  τ₂  g₁  g₂
z₁ : [  0,  0,  0,  0,  0,  0 ]
z₂ : [  1,  1,  1,  1,  1,  1 ]
τ₁ : [  0,  1,  1,  0,  0,  0 ]   indicator of {τ₁, z₂}
τ₂ : [  0,  1,  0,  1,  0,  0 ]   indicator of {τ₂, z₂}
g₁ : [  1,  5,  3,  2,  4,  5 ]   non-classifier; row on core = σ on core
g₂ : [  0,  4,  3,  2,  4,  5 ]   non-classifier
```

Roles: 0 = z₁, 1 = z₂, 2 = τ₁, 3 = τ₂, 4 = g₁ (= sec under strong S,
σ-realiser), 5 = g₂ (= ret under strong S). σ = (τ₁ τ₂) swaps the two
classifiers, fixing both absorbers and both non-classifiers. ρ = g₁
realises σ via its row on core: σ on core = (3, 2, 4, 5) = T[g₁][2..5].
σ² = id; |Aut| = 2.

Strong S: sR = 4 (g₁), rR = 5 (g₂), sR ≠ rR. So unlike at N=5 (where
strong S is unsatisfiable), the joint canonical N=6 witness *can*
have strong S.

## Interpretation

The two structural principles that selected the N=5 canonical witness
do extend to N=6. Concretely:

  - The shape generalises naturally: cls=2, ncl=2 at N=6 (vs cls=2,
    ncl=1 at N=5). The classifier-swap structure is preserved; what's
    added is a second non-classifier.
  - σ swaps the two indicator classifiers, exactly as at N=5.
  - ρ = g₁ realises σ as the row action on core, exactly as at N=5.
  - The second non-classifier g₂ "fills in" the larger core; the
    strong-S retraction pair becomes (g₁, g₂) with g₁ ≠ g₂.

Strong S becoming satisfiable in the joint canonical witness is the
qualitative novelty at N=6. At N=5 the structure theorem forces sec =
ret (paper Cor 4.10); at N=6 the joint canonical witness has strong S
naturally — the second non-classifier accommodates it without breaking
the other canonical structure.

The N=6 joint canonical witness shown above is a candidate "the"
canonical N=6 S+D+C magma. Whether it's unique up to absorber-preserving
isomorphism in the strong-S regime, and whether the principles extend
to N=7+, are the natural follow-up questions.

## Reproducing

    python3 scripts/n6_self_symmetric_search.py
    python3 scripts/n6_joint_canonical_search.py

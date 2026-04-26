# The N=9 Canonical-Witness Lisp Substrate

A 9-element finite magma that simultaneously satisfies:

1. The structural axioms of an extensional 2-pointed magma with classifier
   dichotomy and internal composition (S+D+C, the paper's setting).
2. The canonical-witness symmetry-internalisation property: a non-trivial
   automorphism σ ∈ Aut(M) is realised by left-multiplication by an
   element of M.
3. A complete atomic substrate for Ψ-Lisp-style semantics — Q (quote),
   E (eval), f (car), g (cons), η (cdr), ρ (cond), τ (atom-tester) — all
   present as named distinct primitives.
4. Power-associativity: every element a satisfies a·(a·a) = (a·a)·a.

It's the smallest magma we've found that hosts the homoiconicity backbone
(Q/E retraction) and the canonical-witness symmetry-internalisation
together with all of Lisp's atomic primitives.

## The table

```
        z₁  z₂  g   τ   Q   f   E   η   ρ
z₁  : [  0,  0,  0,  0,  0,  0,  0,  0,  0 ]    NIL absorber
z₂  : [  1,  1,  1,  1,  1,  1,  1,  1,  1 ]    T   absorber
g   : [  8,  8,  8,  2,  7,  6,  5,  4,  2 ]    cons (constructor)
τ   : [  0,  1,  0,  1,  0,  0,  0,  0,  0 ]    indicator classifier
Q   : [  1,  0,  3,  2,  4,  8,  6,  5,  7 ]    quote
f   : [  3,  3,  4,  6,  5,  7,  2,  2,  6 ]    car (first projection)
E   : [  1,  0,  3,  2,  4,  7,  6,  8,  5 ]    eval
η   : [  3,  3,  6,  4,  2,  2,  7,  5,  4 ]    cdr (second projection)
ρ   : [  0,  8,  2,  3,  6,  7,  4,  5,  8 ]    cond / σ-implementer
```

Atom indices: z₁=0, z₂=1, g=2, τ=3, Q=4, f=5, E=6, η=7, ρ=8.

## Roles

| Atom | Lisp role | Class | σ behaviour |
|------|-----------|-------|------------|
| z₁ | NIL / "false" | absorber | fixed |
| z₂ | T / "true" | absorber | fixed |
| g | `cons` (pair constructor) | non-classifier | fixed |
| τ | atom-predicate / `eq` for τ | classifier (indicator-style) | fixed |
| Q | `quote` (suspends evaluation) | non-classifier | swapped with E |
| f | `car` (first projection) | non-classifier | swapped with η |
| E | `eval` (resumes evaluation) | non-classifier | swapped with Q |
| η | `cdr` (second projection) | non-classifier | swapped with f |
| ρ | `cond` (branch) + canonical-witness σ-implementer | non-classifier | fixed |

## The canonical symmetry

The non-trivial automorphism σ has cycle structure

  σ = (f η)(Q E),  order 2

— a product of two disjoint transpositions. It swaps the two natural Lisp
dualities and fixes the asymmetric singletons:

- **σ-paired atoms** (Lisp's natural dualities):
  - **car ↔ cdr** — the two projections of a cons cell.
  - **quote ↔ eval** — the homoiconicity inverse pair.
- **σ-fixed atoms** (Lisp's unique-role primitives):
  - **cons** — the single constructor (no dual partner).
  - **cond** — the single branch primitive.
  - **τ** — the single atom-tester / boolean indicator.
  - **z₁, z₂** — the boolean values themselves.

The σ-orbit structure thus matches Lisp's actual semantic role-arity:
σ-paired iff naturally dual, σ-fixed iff structurally unique.

### σ is internalised in the magma

The defining canonical-witness property is that σ is *realised* by an
element of the magma. Specifically, ρ's row on the core `{2,3,4,5,6,7,8}`
*is* σ acting on the core:

  Row of ρ on core (cols 2–8): `(2, 3, 6, 7, 4, 5, 8)`
  σ on core (σ(2..8))         : `(2, 3, 6, 7, 4, 5, 8)`

So the magma's automorphism is one of the magma's own row functions.
This is the structural property the paper introduces as the canonical-
witness selection principle: "the operation contains its own symmetry."

### Q and E are mutual inverses on the full carrier

The QE retraction strengthens to a bijective involution at the table
level:

  ∀ x ∈ Fin(9):  E·(Q·x) = x  AND  Q·(E·x) = x

Quote and eval are not just one-direction inverses on core — they
form a bijective pair on the entire 9-element carrier, σ-equivariantly
(since σ swaps them).

## Bonus algebraic identities

Six identities fall out of the joint constraints (canonical-witness +
indicator classifier + QE retraction + power-associativity + σ-pairings),
none of which were imposed directly:

| Identity | Reading |
|----------|---------|
| **f² = η** | car squared (atomically) lands on cdr |
| **η² = f** | cdr squared lands on car |
| **Q² = Q** | quote is atomically idempotent |
| **E² = E** | eval is atomically idempotent |
| **g² = ρ** | cons squared lands on cond |
| **ρ² = ρ** | cond is atomically idempotent |

Three of Lisp's control primitives — Q, E, ρ — satisfy the cleanest
possible self-equation (a² = a). The two projections (f, η) form a
"swap-by-squaring" pair compatible with σ. The constructor's square
g² lands on the branch primitive ρ.

These are *consequences*, not axioms. The Z3 solver was asked only for
the joint structural constraints; the algebra produced these identities
on its own.

## What this substrate is and isn't

**Is**: a candidate atomic substrate for a Ψ-Lisp-style language with
canonical-witness symmetry. Smaller than Ψ₁₆ᶠ (9 vs 16 elements).
Algebraically tighter (Ψ₁₆ᶠ is rigid; this has σ as an internal
symmetry with bonus idempotents).

**Is not**:
- A complete Lisp by itself. The Lisp semantics live in a term-level
  evaluator (`psi_eval` style) that dispatches on the atomic tags. The
  table provides primitives; the evaluator provides the language.
- Unique. Other SAT solutions for the same axiom system exist; this is
  one canonical-witness magma satisfying these constraints, not "the"
  one.
- Necessarily computationally optimal. The tighter symmetry might or
  might not buy practical Lisp invariants worth exploiting — that's an
  empirical question for whoever builds the evaluator.

## Relationship to Ψ-Lisp's Ψ₁₆ᶠ

| Property | Ψ₁₆ᶠ | This substrate (N=9) |
|----------|------|----------------------|
| Carrier size | 16 | 9 |
| Automorphism group | trivial (rigid) | Z/2 (σ = (f η)(Q E)) |
| Indicator classifiers | 0 | 1 (τ) |
| Q,E mutual inverses on carrier | partial (8/16) | yes (full) |
| Y atom | named, but row is decorative | not present (term-level only) |
| Power-associativity | yes | yes |
| Named primitives | ⊤,⊥,Q,E,τ,f,g,η,ρ,Y + unnamed | z₁,z₂,Q,E,τ,f,g,η,ρ |

Ψ₁₆ᶠ optimises for "every atom has a unique algebraic role; no permutation
freedom." This substrate optimises for "the magma's symmetry is one of
its operations." Different design objectives; both are coherent.

## Verification

The table was found by `scripts/n9_lisp_natural_duality.py`, which encodes:

- E2PM base axioms (extensionality, two absorbers, no other absorbers).
- S (retraction pair existence).
- D (classifier dichotomy with indicator pattern for any classifier).
- C (ICP — at least one non-trivial composition closure on core).
- Power-associativity.
- Self-symmetric automorphism σ realised by ρ.
- Q, E section-retraction with Q ≠ E, both ≠ ρ.
- f, g, η as distinct named non-classifier atoms.
- σ explicitly imposes σ(f) = η, σ(η) = f, σ(Q) = E, σ(E) = Q.

Z3 finds SAT in 3.7 seconds. The bonus algebraic identities are then
verified post-hoc by direct lookup.

To reproduce:

    python3 scripts/n9_lisp_natural_duality.py

## Open questions

1. **Build a working evaluator.** Adapt `psi_eval`'s dispatch from
   Ψ₁₆ᶠ's atom indices to this table's indices, and verify it can run
   small Lisp programs (factorial, list reverse, meta-circular eval).
   If it works, you have a Futamura-capable Lisp at 9 atoms with
   canonical symmetry.
2. **Exploit σ in proofs.** The σ-equivariance gives an automatic
   "anything proven about an expression also holds for its σ-image."
   What does that buy concretely? Possibly cleaner partial-evaluation
   theorems, possibly nothing useful — depends on whether σ-orbits
   correspond to programmer-meaningful transformations.
3. **Uniqueness.** Is this substrate unique up to absorber-preserving
   isomorphism among 9-element magmas satisfying all the listed axioms?
   We haven't checked.
4. **Scaling.** At larger N, the same axiom set admits more SAT models.
   What additional structure (more idempotents? richer symmetries?)
   becomes available at N=10, 12, 16?

The 9-element table is one design point on a larger landscape; whether
it's *the* right substrate or just *a* coherent one is the next question
to settle.

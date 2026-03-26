# Pairwise Independence of Representation, Classification, and Composition in Finite Extensional Magmas

Lean 4 formalization and SAT reproduction scripts for the paper.

## Result

Three algebraic properties of finite extensional 2-pointed magmas — self-representation (R), the classifier dichotomy (D), and the Internal Composition Property (H) — are pairwise independent. Six Lean-verified counterexamples (sizes 5–10) establish all six non-implications. The optimal coexistence witness has N=5, which is tight: ICP requires 3 pairwise distinct core elements, so N ≥ 5.

## Building

```bash
lake build          # builds all 11 files, verifies 80+ theorems, zero sorry
```

Requires Lean 4.28.0 and Mathlib v4.28.0 (pinned in `lean-toolchain` and `lakefile.lean`).

## Proof inventory

| File | Thms | Style | Content |
|------|------|-------|---------|
| CatKripkeWallMinimal | 17 | Algebraic | Decomposition, bounds, classifier wall |
| NoCommutativity | 3 | Algebraic | Asymmetry |
| Functoriality | 4 | Algebraic | Invariance under isomorphism |
| SelfSimulation | 5 | Algebraic | Partial application injectivity |
| ICP | 20 | Alg.+decide | ICP ↔ Compose+Inert |
| Countermodel | 5 | decide | S ⊬ D (N=8) |
| Countermodels10 | 9 | native_decide | D ⊬ H, H ⊬ D (N=10) |
| E2PM | 10 | decide | D ⊬ S (N=5), H ⊬ S (N=6), S ⊬ H (N=6) |
| Witness5 | 3 | decide | S+D+H at N=5 (optimal), no ICP at N=4 |
| Witness6 | 3 | decide | S+D+H at N=6 |
| Witness10 | 6 | native_decide | S+D+H at N=10 |
| **Total** | **80** | | |

Note: `SelfSimulation.lean` (5 additional theorems on partial application injectivity) is included in the repository but not referenced by the paper.

Proof styles: *Algebraic* = pure equational reasoning, no `decide`. *decide* = kernel computation (N ≤ 8). *native_decide* = compiled native code (N = 10).

## Independence structure

No capability implies any other — all six pairwise non-implications are Lean-proved:

|  | R | D | H |
|--|---|---|---|
| **R** | — | ⊬ (N=8) | ⊬ (N=6) |
| **D** | ⊬ (N=5) | — | ⊬ (N=10) |
| **H** | ⊬ (N=6) | ⊬ (N=10) | — |

Entry (X, Y) = "X does not imply Y", with counterexample size.

Counterexample details:

| Direction | Size | File |
|-----------|------|------|
| S ⊬ D | N=8 | Countermodel.lean |
| S ⊬ H | N=6 | E2PM.lean |
| D ⊬ S | N=5 | E2PM.lean |
| D ⊬ H | N=10 | Countermodels10.lean + ICP.lean |
| H ⊬ S | N=6 | E2PM.lean |
| H ⊬ D | N=10 | Countermodels10.lean + ICP.lean |

## SAT reproduction

```bash
python3 sat/n5_rdh_unsat.py       # N=5 R+D+H: algebraic analysis + Z3 confirmation
python3 sat/n5_rdh_check.py       # N=5 R+D+H: direct Z3 SAT check
python3 independence_results.py          # generate and verify all counterexamples
```

Frozen counterexample tables in `counterexamples.json` allow re-verification without Z3.

## Paper

The paper is in `paper/main.tex` ([PDF](paper/main.pdf)).

## Companion repository

The full project — reflective tower, Ψ-Lisp, supercompiler, compilation, 16-element artifact — is at [github.com/stefanopalmieri/Kamea](https://github.com/stefanopalmieri/Kamea).

## License

MIT

# Splitting, Dichotomy, and Composition in Finite Extensional Magmas: Independence, Connecting Axioms, and a Canonical Eight-Element Model

Lean 4 formalization and SAT reproduction scripts for the paper.

## Result

Three algebraic properties of finite extensional 2-pointed magmas — internal splitting (S, a retraction pair), the classifier dichotomy (D), and internal composition (C, the Internal Composition Property) — are pairwise independent, and jointly irredundant: all eight Boolean profiles of (S, D, C) are realized. Every one of the six non-implications has a Lean-verified counterexample at its **provably minimal size** (N=4 or N=5), and explicit parametric families realize every non-implication and every Boolean profile at **every admissible carrier size**, so neither result is a small-size artifact. The optimal coexistence witness has N=5, which is tight: ICP requires 3 pairwise distinct core elements, so N ≥ 5.

## Building

```bash
lake build          # builds all 37 files, verifies ~435 theorems, zero sorry
```

Requires Lean 4.28.0 and Mathlib v4.28.0 (pinned in `lean-toolchain` and `lakefile.lean`).

## Proof inventory

| File | Thms | Style | Content |
|------|------|-------|---------|
| Dichotomic | 20 | Algebraic | Decomposition, bounds, classifier-dichotomy boundary |
| NoCommutativity | 4 | Algebraic | Asymmetry |
| OneSidedSeparation | 3 | decide | One-sided vs mutual-inverse retraction |
| Functoriality | 4 | Algebraic | Invariance under isomorphism |
| CapabilityInvariance | 4 | Algebraic | S, D, C each invariant |
| ICP | 20 | Alg.+native | ICP ↔ Compose+Inert |
| DStruct | 1 | Algebraic | Axiom reduction: D_struct + ICP |
| Countermodel | 5 | decide | S ⊬ D (N=8, separated roles; superseded) |
| Countermodels10 | 9 | native_decide | D ⊬ C, C ⊬ D (N=10) |
| E2PM | 19 | decide | D ⊬ S (N=4 tight), C ⊬ S, C ⊬ D (N=5 tight), S ⊬ C (N=6) |
| **TightWitnesses** | 18 | decide | **S ⊬ D, S ⊬ C, S+D ⊬ C — all tight at N=5** |
| Witness5 | 3 | decide | S+D+C at N=5 (optimal), no ICP at N=4 |
| Witness6 | 3 | decide | S+D+C at N=6 (s ≠ r) |
| Witness10 | 6 | native_decide | S+D+C at N=10 |
| WitnessAllN | 25 | Algebraic | S+D+C at every N ≥ 5 |
| **IndependenceAllN** | 36 | Algebraic | **All six non-implications and all 8 cube cells at every size** |
| **CompletenessWall** | 10 | Algebraic | **K-infinity; combinatorial completeness excludes D (any cardinality); the finite flip wall: two absorbers alone exclude column-naming finitely** |
| **Sorting** | 28 | Alg.+decide | **Sorted magmas (the first connecting axiom): involution, four class-tables, balance, preserving world at every N** |
| **Homoiconic** | 14 | Alg.+decide | **Introspection fixes the quotation law; the canonical N=6 Lisp kernel** |
| **ArtifactN8** | 16 | decide | **The canonical N=8 artifact: kernel + hygienic shift, lex-min of a 168-table space (law set incl. no-internal-dispatch)** |
| **StackAForced** | 4 | Algebraic | **The frame derived: observable quotation forces the swap world; the frame forces N ≥ 8 (sharp)** |
| **EvalSideFree** | 8 | Algebraic | **Quote-side laws transport to eval through the retraction: hygiene's eval half and eval-side judge-closure are free** |
| **QuoteOrbit** | 7 | Algebraic | **Reversibility free (finite order), order even in the swap world, judge-closure = orbit realization** |
| **Factorization** | 7 | Alg.+decide | **Driver metacircularity: eval(quote p) = run p, base case = the certified table law** |
| **FactorizationEnv** | 10 | Alg.+decide | **Metacircularity with environments (R7RS two-argument eval), conservative over the minimal form** |
| **FactorizationClos** | 15 | Alg.+decide | **Metacircularity with closures: β, fuel, certified divergence (Ω), conservative again** |
| **FactorizationCtrl** | 20 | Alg.+decide | **The System L machine: μ/call-cc, escape demo, big-step→machine simulation, Ω as a 5-state cycle** |
| **FactorizationStore** | 19 | Alg.+decide | **CESK completed: store threaded vs env captured, mutation-through-β, lockstep bisimulation conservativity** |
| **FactorizationData** | 27 | Alg.+decide | **Pairs on the tape, dispatch, certified homoiconicity: programs build their own quotations** |
| **FactorizationEqv** | 26 | Alg.+decide | **The eqv? core form: atomic identity — element identity = observational equality (table extensionality), location identity = R7RS "same location"; null? definable; conservative again** |
| BooleanCube | 25 | decide+native | Joint irredundance: all 8 cells of (S,D,C) |
| Rigidity | 6 | decide+native | Role rigidity of principal witnesses |
| RigidityPartial | 1 | Algebraic | Partial rigidity maps |
| StructureN5 | 8 | Algebraic | N=5 structure theorem: role lock-in, no strong S |
| MirrorRow | 1 | Algebraic | N=5 automorphisms fix absorbers, \|Aut\| ≤ 2 |
| SelfSimulation | 5 | Algebraic | Partial application injectivity (supplementary) |
| KameaRef | 1 | Algebraic | Reference oracle for the Rust host: store-observing loop agrees with the certified loop (supplementary) |
| **AdequacyTags** | 11 | decide | **Adequacy campaign rung 0: META's extensional tag-discrimination trees — matrix, partition of unity, four probes suffice, honesty lemma (ADEQUACY.md)** |
| **Total** | **449** | | |

Proof styles: *Algebraic* = pure equational reasoning, no `decide` (universally quantified results hold for all N). *decide* = kernel computation (N ≤ 8). *native_decide* = compiled native code (N = 10).

## Independence structure

No capability implies any other — all six pairwise non-implications are Lean-proved at their minimal sizes, and at every size above:

|  | S | D | C |
|--|---|---|---|
| **S** | — | ⊬ (N=5, tight) | ⊬ (N=5, tight) |
| **D** | ⊬ (N=4, tight) | — | ⊬ (N=4 tight; N=5 structural) |
| **C** | ⊬ (N=5, tight) | ⊬ (N=5, tight) | — |

Entry (X, Y) = "X does not imply Y", with minimal counterexample size.

Counterexample details:

| Direction | Size | Tightness | File |
|-----------|------|-----------|------|
| S ⊬ D | N=5 | tight (non-vacuous failure needs 3 core roles) | TightWitnesses.lean |
| S ⊬ C | N=5 | tight (structural: ICP formulable only for N ≥ 5) | TightWitnesses.lean |
| D ⊬ S | N=4 | tight (D needs N ≥ 4) | E2PM.lean |
| D ⊬ C | N=4 | tight (vacuous); N=5 structural, also with S+D | ICP.lean, TightWitnesses.lean |
| C ⊬ S | N=5 | tight (ICP needs N ≥ 5) | E2PM.lean |
| C ⊬ D | N=5 | tight (ICP needs N ≥ 5) | E2PM.lean |

The three walls: `CompletenessWall.lean` formalizes K-infinity (no finite carrier with ≥ 2 elements admits a k-combinator), the completeness wall (no total applicative structure of *any* cardinality with two absorbers and s/k combinators satisfies the dichotomy — D's own axioms provide a mixed column, and completeness transposes it into a mixed row), and the finite flip wall (a finite magma with two *distinct* left absorbers cannot internalize every column as a row — at finite scale the transposition hypothesis is itself unsatisfiable, no dichotomy needed; engine: finite-orbit pigeonhole + transposition, no diagonal; see `docs/lawvere-diagonal-and-the-walls.md` for how this positions the walls against Lawvere's fixed-point theorem). Finite worlds cannot be complete — with two halt channels they cannot even name their own columns; complete worlds cannot be dichotomic: the S/D/C landscape is precisely the sub-complete regime, which is why it is invisible from inside the λ-calculus.

Scaling: `IndependenceAllN.lean` proves — algebraically, uniformly in n — that each of the six non-implications has a witness of size exactly n for every n ≥ 5, and that each of the eight (S, D, C) Boolean profiles is realized at every admissible size (`independence_all_N`, `boolean_cube_all_N`). Together with `WitnessAllN.lean` (S+D+C at every N ≥ 5), this settles the scaling conjecture.

The connecting axiom: `Sorting.lean` begins the theory of what entangles the capabilities. **Sorting** (the Z/C/N class map is compositional on core — "the other half" of the type discipline D starts) is proved independent of S+D+C even at N=5 (`sorting_independent`), and the involution theorem (`sorted_involution`) shows S cuts the sorted worlds to exactly two: class-preserving (realized by witness5) and class-swapping (realized at N=6 by a witness whose section exchanges the judge and data blocks — the algebraic shadow of quotation). All four conceivable class-tables are realized (id, swap, const-C, const-N), and S permits exactly the involutive two: the constant worlds provably exclude retraction pairs (`constC_blocks_retraction`, `constN_blocks_retraction`). The swap world forces |C| = |N| (`swap_balance`), hence an even core — within S+D+C it exists only at even N ≥ 6 — while the class-preserving world exists at every N ≥ 5 (`witnessAllN_sorted`: the canonical scaling family is sorted). Under the computational reading — preserving as typing, swapping as quotation — the typed world is available at every size; the quoting world demands exact balance between judges and data.

Homoiconic introspection: `Homoiconic.lean` proves that an internal sort predicate (`data?`/`judge?`) has its quotation law *determined* by the world — negating under quote in the swap world, transparent in the preserving world, with the wrong pairing impossible (SAT-confirmed UNSAT at N = 6..16, then Lean-proved). The canonical N=6 kernel (`canonical_kernel`) realizes the full stack — halt states, quote, eval, `data?`, `judge?` — with the single internal composition being the homoiconicity law `judge? = data? ∘ quote`, and quotation of order 4.

## SAT reproduction

```bash
python3 sat/n5_rdh_unsat.py       # N=5 S+D+C: algebraic analysis + Z3 confirmation
python3 sat/n5_rdh_check.py       # N=5 S+D+C: direct Z3 SAT check
python3 independence_results.py   # generate and verify all counterexamples
```

Frozen counterexample tables in `counterexamples.json` allow re-verification without Z3.

## Paper

The paper is in `paper/main.tex` ([PDF](paper/main.pdf)).

## Companion repositories

- [**kamea-machine**](https://github.com/stefanopalmieri/kamea-machine) — the running artifact: a Rust host for the certified CESK machine (`Magma/Factorization*.lean`), differentially pinned to the Lean semantics, with a REPL, `syntax-rules`, and a self-interpreting metacircular evaluator. Lean is upstream: semantic changes land here first.
- The pearl write-up of the machine ladder ("WispyScheme: Metacircularity as a Theorem") is in `pearl/main.tex` ([PDF](pearl/main.pdf)); the machine architecture rationale is in `MACHINE.md`.
- [Kamea](https://github.com/stefanopalmieri/Kamea) (historical) — the project's original home, now trimmed to the Ψ-16 compiled reflective tower demo; its theory was the ancestor of this formalization.

## License

MIT

# Splitting, Dichotomy, and Composition in Finite Extensional Magmas: Independence, Connecting Axioms, and a Canonical Eight-Element Model

Lean 4 formalization and SAT reproduction scripts for the paper.

## Result

Three algebraic properties of finite extensional 2-pointed magmas — internal splitting (S, a retraction pair), the classifier dichotomy (D), and internal composition (C, the Internal Composition Property) — are pairwise independent, and jointly irredundant: all eight Boolean profiles of (S, D, C) are realized. Every one of the six non-implications has a Lean-verified counterexample at its **provably minimal size** (N=4 or N=5), and explicit parametric families realize every non-implication and every Boolean profile at **every admissible carrier size**, so neither result is a small-size artifact. The optimal coexistence witness has N=5, which is tight: ICP requires 3 pairwise distinct core elements, so N ≥ 5.

## Building

```bash
lake build          # builds all 57 files, verifies ~734 theorems, zero sorry
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
| **MetaImage** | 1 | native | **Adequacy campaign rung 1: the frozen core image of META (~700 nodes), cross-pinned to the Rust compiler through the shared token grammar** |
| **AdequacyRep** | 21 | Algebraic | **Adequacy campaign rung 2: the representation relation (tagged ↔ direct, mutual with environments, monotone in the continuation relation), the one-tape store alignment (canonical `i ↦ K₀+i`), and the eqv-free domain = range of the certified embed** |
| **AdequacyInstances** | 35 | native | **Adequacy campaign rung 3a: 16 end-to-end instances — the frozen image executes inside the proofs and every result stands in the rung-2 relation to the direct run (error defaults, store offset, host callcc, closure clause all observed)** |
| **AdequacyStartup** | 7 | rfl+native | **Adequacy campaign rung 3b(i): the startup lemma — 1275 symbolic machine steps of knot setup verified by kernel reduction, for every environment and continuation; K₀ = 14 becomes a theorem; the entry theorem gives every adequacy run the same canonical meval-entry state** |
| **AdequacyLeaf** | 5 | rfl+native | **Adequacy campaign rung 3b(ii): the leaf forms universally — variables over ALL indices by one symbolic kernel reduction (the 144-step run never inspects the numeral; both worlds miss, related), atoms over all eight by fin_cases (the retraction eatom∘qatom = id, recomputed by the interpreter)** |
| **AdequacyBeta** | 5 | rfl+native | **Adequacy campaign rung 3b(iii): β by families — the identity on any variable (infinite, one rfl), K on any two variables (doubly infinite), nested redexes, a closure returned through β (RepV.clos on a compound run), and β delivering all eight atoms** |
| **AdequacySim** | 31 | rfl+Algebraic | **Adequacy campaign rung 3b(iv): the general simulation induction — universal adequacy for the applicative fragment. META's internal calling convention extracted self-computingly (meval = knot cell 9, curried; mnth = cell 8); a dispatch kit of symbolic kernel reductions (β-application in three phases with self-computing continuation transformers, the apply phase a tail call); mnth simulates chainNth by induction; the machine's table product fires *naked* mid-interpretation, making all 64 magma products one reduction; every error arm agrees. Master theorem by induction on big-step derivations; corollaries: closed-program adequacy, the interpreted magma is the magma, and id-towers of unbounded depth — adequacy infinite in program structure** |
| **AdequacyData** | 32 | rfl+Algebraic | **Adequacy campaign rung 4: the data forms join the simulation induction — `EvD` extends the big-step relation with cons/car/cdr/pairp/ite arm-for-arm against the machine (including all three ite branches and every error arm); cons is the application pattern in miniature ending in a 2-step symbolic pack; car/cdr/pairp dispatch on the result tag with payloads as passengers; every branch call is a tail call so the empty continuation relation still suffices; the pure cases reuse the 3b(iv) kit verbatim. Corollaries: 10-form closed-program adequacy, adequacy for every quoted list (infinite in data structure), the constructor/projector roundtrip for all 64 pairs** |
| **AdequacyStoreKit** | 57 | rfl+Algebraic | **Adequacy campaign rung 5 (kit): every dispatch lemma of rungs 3b(iv)/4 restated over a store with a symbolic suffix — each rfl certifies its segment never touches the live store — plus the store forms' segments: ref's allocation is the machine's own refK arm at any store (the canonical location map is the allocation rule, not bookkeeping), deref's read and setref's write are naked machine arms with index/value/store symbolic, and every store error arm agrees** |
| **AdequacyStore** | 9 | rfl+Algebraic | **Adequacy campaign rung 5: the store forms join the induction — EvS threads stores through all 22 clauses arm-for-arm; meval_simS carries rung 2's alignment as its invariant (META's store = knot prefix + pointwise-represented image, locations at K₀+i for free); the written value is the campaign's first non-passenger (META's post-write closure captures it — the rfl refuted the dummy extraction); deref carries an in-bounds premise (out-of-bounds defaults differ in kind — naked vs tagged — unreachable for machine-created locations). Corollaries: 12-form closed-program adequacy with related final stores, the store roundtrip (all 8), allocate-overwrite-return (all 64)** |
| **AdequacyComplete** | 12 | Algebraic | **Adequacy campaign rung 5½: completeness and well-formedness — a terminating machine run of a control-free program IS a derivation (induction on fuel; sub-runs re-fueled by monotonicity), with store well-formedness preserved through all 22 clauses (locations bounded, stores only grow), discharging rung 5's in-bounds premise: out-of-bounds reads are provably unreachable from closed programs. Headline: meta_inherits_convergence — the interpreted world converges whenever the direct world does, from the run itself, no derivation hypothesis** |
| **AdequacyCtlKit** | 11 | rfl+native | **Adequacy campaign rung 6 (kit): control — the callcc absorption certified (132-step tail call, the captured continuation literally the base κ, shf-tagged onto the environment: the machine's callcc arm one level up); the throw (260 steps, tagged value delivered verbatim: the cont-application arm one level up); seven continuations-as-values arms all agreeing with the machine; and meta_eqvFree — the frozen image is itself in the 13-form domain, the gateway to the tower** |
| **AdequacyEntry** | 1 | rfl | **Adequacy campaign rung 6 (entry): the ρ₀-general 17-step entry into the calling convention — the tower program evaluates META from the empty environment, and this carries it in** |
| **AdequacyControl** | 33 | Algebraic | **Adequacy campaign rung 6: the small-step simulation — KRel pairs every direct frame with its certified continuation transformer (continuation representation IS the dispatch architecture); sim_step matches every machine step with a nonempty META segment (callcc hands the KRel evidence over directly, the throw is the cont-application arm one level up); sim_run/sim_diverge give two-sided behavior transfer; adequacy_ctl covers the full 13-form domain including callcc; and the tower: tower_step (one interpretation layer as a theorem, self-composing) and tower (collapse at every height — the two-level demo becomes the k = 2 instance of an induction)** |
| **AdequacyTop** | 4 | Algebraic | **Adequacy campaign rung 7 — the top theorem, and the campaign closes: interpreter_adequacy (a monotone fuel transformer under which META's run tracks the direct run — convergence within n direct steps becomes convergence within F n META steps to a representing value, divergence transfers); halts_iff (the interpreted program halts iff the program halts); observable_agreement (element results are determined: the interpreter answers with exactly the tagged quotation); law_lift (machine-equal programs are interpreted-equal — every certified law lifts with no new proofs). With rung 6's tower, all four corollaries of the plan's §0 are theorems** |
| **KernelConsumption** | 9 | Alg.+decide | **The consumption lemmas: META's atom case spends S, D, C — one law each, at the proof-term level. leafSpec transcribes the interpreter's three-probe atom branch; probe 1 reads the sort (D — proved from artifactA8_introspection + the dichotomy), probe 2 is the ICP composite judge? = data? ∘ quote (C — proved from artifactA8_icp_through_quote, with row 6 the unique code/absorber separator), the payoff is eval, correct by the retraction (S — spends eatom_qatom); meval_atom_runs_leafSpec bridges to the certified atom reduction; witness classifications: every ICP realization in the N=6 kernel and the artifact IS the homoiconicity law** |
| **ParityN8** | 7 | decide | **The parity grading of the core actions: quote/eval share one action, the closure of the realized actions is Klein-four, and neither even element is a row — no internal no-op (the quote²-exclusion as a kernel theorem at N=8), the cycle-swap driver-side at cost exactly two; shift = quote twisted by the cycle-swap. Diagram: docs/parity-grading.png** |
| **CanonicityCensus** | 3 | native | **The canonicity census, certified: Aut(A8) = 1 (full rigidity — MirrorRow's ≤ 2 sharpened, all 40,320 permutations decided), and the canonicity theorem at the core block: every self-locating member of the hygienic judge-closed frame family (648 configurations) is conjugate to the artifact — self-location (the judge row on the cycle it judges, γ in its own target, the introspector on the untouched cycle) is the exact separator the census discovered among the 18 orbits** |
| **CoreCanonical** | 2 | Algebraic+decide | **The bridge, formalized — the direct canonicity theorem with no enumeration: ANY magma carrying a hygienic self-locating reflective kernel (retraction, quote involution and core-valuedness, and the intrinsic self-location axioms — the three classifiers are the quotations of the three operators: ⌜quote⌝ recognizes exactly the operators, ⌜shift⌝ recognizes exactly shift and itself, ⌜eval⌝ complements ⌜quote⌝, shift exchanges eval's cycle with its own and fixes quote's) is core-isomorphic to the artifact. All 36 core cells derived structurally; the eight elements proven pairwise distinct; sharpness by decide. The lex-min tie-break is retired: the canonical table is a theorem, not a convention** |
| **Total** | **734** | | |

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

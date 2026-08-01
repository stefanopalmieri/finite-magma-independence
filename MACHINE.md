# The Kamea Machine: Driver Architecture for an R7RS Scheme

**Status**: design decision, 2026-07-22.
**Decision**: the driver is a **call-by-value System L machine with a store** —
operationally a CESK-family machine whose state is a sequent-calculus command
⟨focus ‖ continuation⟩, plus the tape. Krivine is its call-by-name dual and
appears only as thunk-mode for `delay`/`force`.

This document records why, so the choice can be re-derived rather than
re-litigated. Everything marked **[thm]** is Lean-verified in this repository
(zero `sorry`); everything marked **[sat]** is a frozen SAT result with script.

---

## 1. The two-level architecture (forced, not chosen)

- **The magma is microcode, not the machine.** No finite carrier admits a
  k-combinator (K-infinity, `CompletenessWall.lean` **[thm]**), so universality
  lives in an external driver loop over growing state ("the tape"). The table
  is the ALU; each machine step is one Cayley lookup.
- **Data structure is tape-only.** No magma with |core| ≥ 2 has faithful
  internal curried pairing with both projections (pairing wall, pigeonhole;
  UNSAT-confirmed at N=8 **[sat]**), and a faithful constructor cannot have a
  non-trivial internal recognizer of its image (recognizer wall: injective ⇒
  surjective on a finite core **[sat]**). Hence pairs, vectors, strings,
  numbers, environments, continuations, and their type predicates (`pair?`
  etc.) are tape representations + tags. This is why `cons` can be both
  faithful and recognizable in a real Lisp: recognition inspects the heap,
  not instruction identity.
- **User-level `quote`/`eval` are driver operations.** R7RS quote is
  sort-collapsing (everything quoted is data = the constant class-table), and
  constant class-tables provably exclude an internal eval
  (`constN_blocks_retraction`, `Sorting.lean` **[thm]**). So the standard's
  §6.12 `eval` and `quote` operate on tape representations, *underwritten by*
  the table's internal faithful duality (quote = element 2, eval = element 3
  of the artifact). Two quotes, two levels — by theorem, not by convenience.

## 2. The certified instruction table

`Magma/ArtifactN8.lean` (`canonical_artifact_N8`) freezes the canonical N=8
Stack-A artifact: the lexicographically minimal member of the **168**-table
design space determined by the full law set (kernel + faithful shift +
hygiene + judge-closure + no-internal-dispatch; enumeration in `scripts/n8_free_pair_search.py`
**[sat]**).

```
     0  1  2  3  4  5  6  7
  0 [0, 0, 0, 0, 0, 0, 0, 0]   halt-true   (absorber / accept channel)
  1 [1, 1, 1, 1, 1, 1, 1, 1]   halt-false  (absorber / reject channel)
  2 [0, 0, 5, 6, 7, 2, 3, 4]   quote  (s)  involution i ↔ i+3
  3 [0, 1, 5, 6, 7, 2, 3, 4]   eval   (r)  same core action, marker at col 1
  4 [0, 0, 5, 7, 6, 2, 4, 3]   shift  (γ)  faithful hygiene operator
  5 [0, 0, 1, 1, 1, 0, 0, 0]   data?  (κ)  sort introspection
  6 [0, 0, 0, 0, 0, 1, 1, 1]   judge?      = data? ∘ quote  (the ICP)
  7 [0, 0, 0, 0, 1, 0, 0, 1]   shift?      emergent recognizer of {shift, quote·shift}
```

Certified laws **[thm]**: retraction (eval∘quote = id on core, anchored),
dichotomy, ICP (`judge? = data? ∘ quote`), sorted class-swapping world,
sort-introspection with its *forced* negation law (`data?` answers oppositely
on x and quote·x — `Homoiconic.lean`), shift hygiene (commutes with quote and
eval, involutive, faithful), quote involution, and the emergent duality
pairing: **each operator's code is its judge** (quote↦`data?`, eval↦`judge?`,
shift↦`shift?`).

Law-set reductions **[thm]** (`StackAForced.lean`, `EvalSideFree.lean`):
the swap world and N=8 are *derived* from observable quotation plus a
faithful third operator (`stack_a_frame_min`, sharp), and the eval side
of the law set is free — shift-commutes-with-eval follows from
shift-commutes-with-quote, and eval-side judge-closure follows from
quote-side closure by a finite-orbit argument
(`eval_comm_of_quote_comm`, `eval_closure_of_quote_closure`;
`n8_enumerate_lexmin.py` confirms empirically that dropping the
eval-commutation law leaves the model space unchanged). Further
(`QuoteOrbit.lean`): reversibility of any faithful operator is free
(finite core order, `faithful_finite_order` — iterated quotation
always cycles, `quote_finite_order`); in the swap world the order is
necessarily **even** (`swap_even_order`), so the involution law is
just the choice of the minimal order — a tie-break, not an axiom;
and judge-closure of the introspector's realized quote-orbit is
automatic in both directions (`orbit_quote_closure`,
`orbit_eval_closure`). **Final ledger — derived**: the world, the
size, the eval side, reversibility, even order, orbit closure.
**Still chosen**: quote-commutation (the definition of hygienic),
order = minimum (tie-break), orbit-realization + closure for judges
outside the orbit (at N=8: the one free judge), shift's
action-distinctness, **no-internal-dispatch** (¬W — dispatch is machine
work, adopted 2026-08-01 when the W-probe showed lex-min was silently
deciding it; the artifact is unchanged), and the lex-min tie-break.

Also certified: no element of any swap-world magma realizes quote²
(block-preserving, hence expressible by no row) **[sat]** — derived actions
necessarily live driver-side. **Correction (2026-08-01, W-probe)**: internal
dispatch (W — a generic row glued from two handler rows along a core test;
`scripts/canonicality/probe_dispatch.py`) is *not* excluded by the law set:
60 of the 228 models satisfy it (`w_over_228.py`); the canonical artifact is
among the 168 that do not. "Branching is not a table capability" is therefore
a property of the lex-min *choice*, not of the laws — driver-side `ite` was
bought by the tie-break, unpriced until now. **Resolved (same day)**: ¬W adopted
into the law set (`n8_enumerate_lexmin.py`: 168 models, lex-min still
rawA8; pre-adoption 228 kept as the derivation record). The tie-break
is again semantically inert w.r.t. every capability named so far.

## 3. Why the sequent-machine family (System L / λ̄μμ̃)

"CEK or Krivine?" is really "which polarity of Curien–Herbelin's λ̄μμ̃?":
cut-elimination in its CBN fragment *is* the Krivine machine; the CBV
fragment yields the CEK-family machine. Choose the calculus, then the
polarity. Reasons the calculus is forced-by-fit:

1. **Absorbers are System L's co-constants.** The algebra's two absorbers
   correspond to aborting terms μδ.c; machine-level they are the two toplevel
   continuations. Halting = cutting the focus against accept/reject.
   z·x = z is "a halted command ignores further input."
2. **The swap world is a producer/consumer duality.** Operator/judge blocks,
   exchanged involutively by quote, mirror System L's term/context split under
   its duality involution. A sequent-structured machine makes the two-level
   correctness theorem (driver quote/eval factoring through the table's
   duality) structural rather than coincidental.
3. **Machine dispatch = the table's own introspection.** The step function's
   case-split ("is the focus a producer or consumer?") is computed by the
   `data?` instruction.
4. **R7RS hard requirements are native**: proper tail calls (command steps
   don't grow the stack in tail position — machine shape, not optimization);
   `call/cc` is just μ (binding the current consumer — continuations are what
   the machine is made of); exceptions are cuts against alternative channels.

## 4. Why CBV, why the store

- Scheme is applicative-order ⇒ the **CBV (LKQ) discipline** — the CEK side
  of the duality. `delay`/`force` = CBN pockets as tape thunks, not machine
  architecture.
- R7RS mutation (`set!`, `set-car!`, ports) ⇒ the **S** of CESK: a store on
  the tape.
- Closures and `eval`'s environment argument ⇒ the **E** component. With a
  de Bruijn tape representation, environments are index maps and the
  artifact's `shift` is the certified renaming operator keeping
  `syntax-rules` hygiene lawful under quotation (the frozen hygiene laws).

## 5. Correspondence table

| machine part            | project counterpart |
|-------------------------|---------------------|
| command ⟨v ‖ k⟩         | driver state; halt = cut against absorber channel |
| producer/consumer split | operator/judge blocks; dispatch via `data?` |
| μ (context capture)     | `call/cc` |
| CBV fragment            | applicative order; CBN dual = `delay`/`force` |
| E + S components        | tape: environments, heap, store |
| command reification     | user-level `quote` (driver-side, per §1) |
| toplevel co-constants   | the two absorbers (accept / reject) |

## 6. R7RS obligations, layer by layer

| R7RS requirement | layer | note |
|---|---|---|
| `eval`, `quote`, quasiquote | driver over tape | forced driver-side (§1); underwritten by table duality |
| disjoint types, total predicates | tape tags + driver | discipline is the D+sorting shadow; instruction-level: `data?`/`judge?` with forced negation |
| proper tail calls | machine shape | free from command-loop structure |
| `call/cc`, `dynamic-wind`, exceptions | machine (μ) + tape | winding marks are engineering |
| `syntax-rules` hygiene | `shift` + tape | hygiene laws certified at table level |
| numbers, strings, vectors, ports | pure tape | zero table pressure |

## 7. Methodology: derive, don't design

Match the table's ethos at the machine level via **Danvy's functional
correspondence**: write the R7RS metacircular evaluator, CPS-transform,
defunctionalize — the result lands mechanically in the CEK/CESK family, and
the derivation itself becomes part of the certification story. Every layer
derived: table by lex-min over an enumerated law space, machine by functional
correspondence from the semantics, joined by the factorization theorem.

## 8. Forced vs. engineering

**Forced** (by theorems above): command-shaped state, CBV polarity, external
store/heap, two halt channels, native first-class continuations, driver-level
user quote/eval, table-level hygiene operator.

**Engineering** (no algebraic preference): frame layouts, `dynamic-wind`
winding marks, environment representation, tag encodings, GC.

## 9. Open next steps

1. **The two-level factorization theorem** — minimal form DONE
   (`Magma/Factorization.lean`, `eval_quote`): a driver whose only
   semantic step is a `dotA8` lookup satisfies `eval (quote p) = run p`
   for every program, by an induction whose base case is the artifact's
   certified retraction (`eatom_qatom`). **Environments DONE**
   (`Magma/FactorizationEnv.lean`): de Bruijn variables + the E
   component; `eval ρ (quote p) = run ρ p` for every environment
   (R7RS's two-argument eval), with representation adequacy proved
   environment-free, the shift instruction as the variable tag
   (`quote_var_succ` / `shift_cell_skips_binding` — one shift cell =
   one binding skipped), and conservativity over the minimal form
   (`run_embed`). **Closures/β DONE** (`Magma/FactorizationClos.lean`):
   λ + closures with a fuel-indexed `run`; `eval fuel ρ (quote p) =
   run fuel ρ p` *uniformly in fuel* (converge together, diverge
   together); fuel proved operational-not-semantic (`run_mono_le`);
   Ω certified divergent at every fuel (`Omega_diverges` — K-infinity's
   operational shadow); λ-free programs conservative at fuel ≥ depth
   (`run_embed`); the duality pairing reached metacircularly by β
   (`eval_quote_duality_demo`). Tags: quote (2) = λ, eval (3) = app,
   shift (4) = var. **Control DONE** (`Magma/FactorizationCtrl.lean`):
   the driver is now an actual System L machine — command states
   ⟨focus ‖ continuation⟩, halt = cut against the toplevel co-constant
   (`step_halt`), `callcc` = binder-form μ (`step_mu`), continuation
   invocation = cut against the captured consumer discarding the
   current one (`step_throw`), proper tail calls structural
   (`step_beta`: β keeps the same continuation). `eval_quote` holds
   over the machine uniformly in fuel; escape-through-quotation demo
   certified against the table; big-step → machine simulation theorem
   (`machine_sim`, continuation-polymorphic) + machine determinism =
   two-sided conservativity on μ-free programs; Ω diverges via a
   certified five-state machine cycle. Tag: judge? (6) = μ.
   **Store DONE — item 1 CLOSED** (`Magma/FactorizationStore.lean`):
   the full CESK machine. E captured vs S threaded is certified as
   computation (`eval_quote_mutation`: a `setref` in argument position
   observed by the body through β); continuations provably do not
   restore the store (`step_throw`); allocation/read/write laws +
   `read_alloc`; conservativity strengthened to a **lockstep
   bisimulation** (`step_embed`/`runM_embed`: identical answers under
   `Option.map`, values and divergence alike — Ω transfers free).
   Tags: data? (5) marks store forms, sub-tagged by quote/eval/shift =
   ref/deref/setref. The factorization ladder is complete: minimal →
   env → closures → control → store, each rung conservative, every
   induction grounded in `eatom_qatom`. What remains toward R7RS (§6)
   is breadth, not architecture: data types, numeric tower,
   `syntax-rules`, ports — tape/driver engineering, no new algebraic
   content. **First breadth rung DONE**
   (`Magma/FactorizationData.lean`): pairs on the tape (`cons`/`car`/
   `cdr` build and read heap cells — pairing wall), `pairp` reads heap
   structure (recognizer wall), `ite` as machine dispatch (Branch is
   not a table capability; ff = the only false). Headline: **certified
   homoiconicity** — `programs_build_their_own_quotations`: for every
   program q there is a program computing `quoteD q`; with
   `eval_quote`, eval of the built quotation runs q. Tag: shift? (7)
   sub-tagged 2 cons / 3 car / 4 cdr / 5 pairp / 6 ite — the tag
   space {2..7} is now exactly exhausted. Conservativity over the
   store rung again a lockstep bisimulation. **Second breadth rung
   DONE** (`Magma/FactorizationEqv.lean`): the `eqv?` core form —
   atomic identity. Element identity **is** observational equality by
   the table's extensionality (`eqv_elem_observational`: two
   instructions are eqv?-identical iff their rows coincide — the
   primitive adds speed, not power); location identity is R7RS's
   "same location" (`eqv_fresh_refs`, `eqv_same_ref`), previously
   unobservable. Compounds are never eqv?-identical by design: cells
   are immutable tape values with no location — structural comparison
   is `equal?`'s surface derivation, identity-bearing mutable
   structure is `ref`'s job. `null?` definable at last (`nullp` =
   eqv-with-nil). Tag: shift? sub-tag 7 — the sub-tag space {2..7}
   under shift? now exactly exhausted too. `eval_quote` at 14 syntax
   classes, homoiconicity carried, conservativity over the data rung
   a lockstep bisimulation again; all propext-only. Unblocks the
   kamea-machine README's top remaining item; propagated to the Rust
   host (enum arm, step arms, (7,7) tag in quote/decode, surface
   `eqv?`/`null?`), and `KameaRef.lean` is re-pinned to this rung as
   the difftest oracle — standing run 24,000 cases bit-identical with
   `Eqv` in the fuzz grammar. Next breadth after that:
   `syntax-rules` ports/devices, numeric tower as tape data.
2. **Size escalation criterion**: stay at N=8; move to N=10 only when a
   specific desired law returns UNSAT at 8 (candidate: a certified
   abort/continuation pair, if the exception path should be table-level).
   So far nothing requires it.
3. Optional Lean debt: recognizer wall and pairing wall as abstract theorems
   (currently SAT + hand proof); swap world at all even N (currently N=6
   witness + evenness necessity).

## 10. I/O without atoms (design note, 2026-07-24)

**Decision**: I/O adds **no table elements and no core forms**. The
old Ψ-16 spent atoms on GET/PUT; the current architecture forbids the
move (tag space {2..7} exactly exhausted, table frozen) and doesn't
need it: K-infinity already places the loop outside the algebra, and
I/O is the loop talking to the world. Three driver-level strata, none
touching the certified core:

1. **Batch** (works today, zero changes): driver pre-loads input into
   the initial store/environment, runs to halt, reads output from the
   result value and final store. The Lean semantics as-is.
2. **Memory-mapped** (hardware-natural): designated store locations
   act as device registers — `deref`/`set-ref!` on them reach the
   world by *driver* convention. In discrete hardware this is free
   (address decoder routes top store locations to a UART); on an MCU
   it is the effect-handler table.
3. **Request/resume via callcc** (the principled interactive one):
   wrap programs in a toplevel continuation capture; `(read)`,
   `(display e)`, `(gpio-set p v)`, … macro-expand to throwing
   `(cons request-tag (cons payload k))` to the root. Driver loop:
   run to halt; if the result is a request cell, perform the effect
   and resume by invoking the carried continuation with the reply;
   else done. Algebraic effects from certified parts: requests are
   cells (data rung), yielding is μ (control rung), resumption is
   `step_throw`, sugar is the expander. Zero new core forms; difftest
   and all theorems untouched. Expected bonus: effects tunnel through
   the metacircular tower, since `meta` absorbs object callcc into
   host callcc — a level-2 `(read)` should reach the real driver
   (verify the resume path with a test before relying on it).

**Certification boundary**: all three strata are driver engineering —
no theorem weakens. A *certified* I/O semantics (eval_quote over
interaction traces, oracle stream threaded like σ) is a possible
future Lean rung, needed only for theorems about interactive
equivalence, not for I/O to work.

## 11. File pointers

- `scripts/psi_lambda_mu_n9.py`, `psi_lambda_mu_n9_v2.py`, `n9_church_2a.py`,
  `LAMBDA_MU_ON_N9.md`, `RESULT_2A.md` — **the driver seed**: a working
  λ̄μμ̃ prototype (polarity involution with σ-fixed cut trigger and
  position-swapping duality; 25/25 σ̂-commutation checks). Built over the
  archived N=9 substrate (`scripts/n9-archive/`); port it to `dotA8`.
- `Magma/ArtifactN8.lean` — the canonical artifact and its 16 certified laws
- `Magma/Homoiconic.lean` — introspection determines the quotation law; N=6 kernel
- `Magma/Sorting.lean` — sorting, involution theorem, four class-tables, swap balance
- `Magma/CompletenessWall.lean` — K-infinity + completeness wall (the two walls)
- `scripts/n8_free_pair_search.py`, `scripts/homoiconic_search.py` — SAT probes/enumeration
- `paper/main.tex` — §Sorted Magmas, §Homoiconic introspection, appendix tables

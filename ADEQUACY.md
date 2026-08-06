# ADEQUACY.md — the interpreter-adequacy campaign

*Plan of record, opened 2026-08-03. Companion to MACHINE.md (which
drove the factorization ladder) and PEARL.md (which drove the paper).
This document drives the sequel theorem: proving the metacircular
evaluator correct **inside Lean**, upgrading the pearl's title from
"certified at the machine, tested at the evaluator" to metacircularity
as a theorem all the way up.*

Status tags: **[lean]** done and certified; **[open]** not started;
**[risk]** known hard part; **[decision]** architectural decision of
record.

---

## 0. The target theorem

> **Interpreter adequacy.** Let `META : Prog` be the frozen core image
> of `META_CLOSED` (§2). For every core program `p`: running
> `META ⬝ ⌜p⌝` on the certified machine agrees with running `p`
> directly — same termination behavior, same value up to the
> representation decode (§3), same store effects up to the alignment
> invariant (§4) — uniformly in fuel: there is a monotone fuel
> transformer `F` with
> `runM (META ⬝ ⌜p⌝) (F n) ≃ rep (runM p n)`, and divergence
> transfers in both directions (the shape of `eval_quote` and the
> ladder's conservativity theorems, one level up).

Corollaries, in order of glamor:

1. **Tower collapse at every height** — apply the theorem `n` times;
   the two-level tower demo becomes the `n = 2` instance of an
   induction.
2. **The interpreted world inherits every certified law** — β, the
   factorization law, call/cc behavior, store discipline — with no
   new proofs.
3. **The adequacy corpus (17 programs) demotes** from evidence to
   regression test.
4. The pearl's sequel exists.

## 1. Trust architecture — what is proved about what

**[decision] Lean proves theorems about a frozen core image, not
about the Rust surface compiler.** `META_CLOSED` is a closed surface
program (letrec + lambda + core forms; no macros). The Lean side has
no surface compiler, and certifying one is a separate campaign. So:

- Run the kamea-scheme compiler once; emit the compiled core `Prog`
  term; freeze it as `Magma/MetaImage.lean` — the same move that
  froze the SAT-derived table into `ArtifactN8.lean`. Derive, don't
  design; then pin.
- Pin the image against drift: `kamea-diff` already echoes parsed
  programs bit-for-bit; add an image-echo case so the difftest fails
  if the Rust compile of `META_CLOSED` ever diverges from the frozen
  Lean term.
- The letrec knot is part of the image: the frozen term begins by
  allocating the recursion cells (Landin's knot on the certified
  store rung). The theorem is about *that* term. Nothing about
  macro-expansion or the reader is in the trust story.

**[decision] META v1 stays extensional.** `eqv?` is now a certified
core form (`FactorizationEqv`), and META predates it. The theorem is
about the frozen image as it exists — extensionality decision trees,
no `eqv?` (`AdequacyTags.lean` certifies the trees). A META v2 using
`eqv?` for tag dispatch is a possible later simplification; it would
be a new image and a re-run of rungs 3–7, not a change of
architecture.

**[decision] The v1 domain is the eqv-free fragment.** Discovered at
rung 2, from the definitions rather than a failed proof: `quoteD`
sub-tags `eqv` as 7 under the data tag, and META's `mdata` tree —
written before the eqv rung existed — reads sub-tag 7 as `ite`. So
META v1 correctly interprets exactly the 13-form fragment. Rather
than patch META now (a new image, a re-freeze), the v1 theorem
quantifies over `EqvFree` programs — and `AdequacyRep.lean` proves
`eqvFree_iff_embed`: the domain is precisely the range of the
certified embedding from the data rung, i.e. the image of the
conservativity ladder, not an ad-hoc predicate. META v2 adds an eqv
arm to `mdata` later and extends the domain; that is a re-run of
rungs 1 and 3–7 over a new frozen image, not a change of
architecture.

**[decision] Lean-first fix loop.** The universal theorem will
almost certainly flush out corner cases the 17-program corpus never
sampled (error-arm mismatches are the likeliest — §5, risk 3). The
discipline when it does: fix `META_CLOSED` in kamea-scheme, re-run
the corpus + difftest, re-freeze the image, resume the proof. The
theorem is allowed to *improve* META; it is not allowed to be about
a META nobody runs.

## 2. The frozen image (rung 1)

Mechanics: a `kamea-scheme` test emits the compiled `Prog` of
`META_CLOSED` in the Lean term grammar; the emitted file is committed
as `Magma/MetaImage.lean`; a difftest case pins it. Expected size:
large but inert (one definition, no proofs). The image's structure
worth naming in docstrings: the knot prefix (cell allocations +
forwarders), the five `letrec`-bound dispatch functions, the
`callcc`-absorption site.

## 3. The representation relation (rung 2)

`rep : Val → Val → Prop` — interpreted (tagged) value on the left,
direct value on the right:

| tagged | direct | notes |
|---|---|---|
| `(quo . e)` | `elem e` | base case; `AdequacyTags` discriminates |
| `(evl . (⌜body⌝ . envT))` | `clos body env` | body via certified `decode_quote`; env pointwise `rep` |
| `(shf . k)` | `cont k'` | **host absorption: the continuation relation, §5 risk 1** |
| `(data? . loc l)` | `loc l'` | through the store alignment (§4) |
| `(judge? . (a . d))` | `cell` components pointwise | |

Plus: `IsTag (car v)` everywhere — the invariant
`tagloc_accepts_ff` proves is not optional.

## 4. Invariants (rung 2, with rung 5 finishing)

**Store alignment.** One tape, shared — but the meta-run's store
holds the knot cells (a fixed prefix) and *tagged* values where the
direct run holds plain ones. Invariant: an order-preserving injection
`α` from direct indices into meta indices, knot prefix excluded,
with `rep (σ_meta[α i]) (σ_direct[i])` pointwise, and allocation
lockstep (each `ref` in the direct run corresponds to exactly one in
the meta run — true by inspection of `mstore`; the proof makes it an
invariant).

**Fuel transformer.** Monotone `F`, as in the ladder — the meta-run
spends a bounded factor per direct step (dispatch trees + knot
dereferences). Uniformity in fuel is the point: convergence and
divergence transfer together.

## 5. Risks, ranked

1. **[risk] The continuation relation.** Object `callcc` absorbs into
   host `callcc`: the interpreted continuation `(shf . k)` captures
   the *meta-run's* continuation at the corresponding point, and the
   relation must say "invoking `k` in the meta-run simulates invoking
   `k'` in the direct run" — a simulation clause over continuations,
   the classic hard case of logical relations for control. Mitigation:
   `FactorizationCtrl`'s `machine_sim` is continuation-polymorphic
   already; its proof pattern (reduced-form konts + fuel-existential)
   is the template. This risk is why rung 6 is scheduled last before
   the top theorem.
2. **[risk] Store bookkeeping.** The alignment invariant is
   conceptually simple and mechanically fiddly (the knot prefix, the
   injection through interleaved allocations). Mitigation: the store
   rung's lockstep bisimulation (`step_embed`/`loop_embed`) shows the
   shape; expect volume, not surprise.
3. **[risk] Error-arm mismatches.** META's fallback arms return
   `(quo . tt)` (accept-absorber representation) in places where the
   direct machine may land differently, and the corpus never probed
   most of them. Expect the proof to fail first here; that failure is
   the theorem earning its keep (→ Lean-first fix loop, §1).
4. **[risk] Image scale.** The frozen term is big; proofs over it
   must be arm-local (never unfold the whole image). The five
   dispatch functions give the natural case structure.

## 6. The rungs

| rung | contents | status |
|---|---|---|
| 0 | Tag discrimination trees certified at table level (`AdequacyTags.lean`, 11 thms: matrix, partition of unity, four-probes-suffice, honesty lemma) | **[lean]** |
| 1 | Frozen image `MetaImage.lean` (~700 nodes) + Rust emitter/pin (`kamea-scheme/tests/meta_image.rs`, golden-tested, closedness-checked) + Lean-side pin (`meta_image_pinned`: total `toTokens` printer reproduces the golden token string, `native_decide`) | **[lean]** |
| 2 | `AdequacyRep.lean` (21 thms): `RepV`/`RepEnv` (mutual, parameterized by `K₀` and an abstract continuation relation `KR`, monotone in `KR` for rung 6's step-indexing); `AlignedStore` (knot prefix + canonical `i ↦ K₀+i`, read/write/alloc/fresh-loc lemmas); `chainNth` env lookup (META's error default *represents* the machine's error default); `IsTag` soundness on all represented values; decode bridge; `EqvFree` domain = range of certified `embed` | **[lean]** |
| 3a | `AdequacyInstances.lean` (35 thms): 16 executable end-to-end instances — the frozen image runs natively *inside the proofs* (`native_decide`) and every result stands in the rung-2 relation to the direct run, by constructor. Observed ahead of the universal proof: error defaults correspond, store offset works, host `callcc` absorption works, the closure clause is exact. Includes the structural comparator `beqV` (+ reflexivity) since `Val`/`Kont` admit no derived `DecidableEq` (mutual + nested `List` defeats the handler). Regression armor for all later rungs. | **[lean]** |
| 3b(i) | `AdequacyStartup.lean` (7 thms): **the startup lemma** — `stepIter`/`loop` fuel-transfer machinery; then 1275 symbolic machine steps of knot setup verified by *kernel reduction* (`rfl`, ~14 s at `maxRecDepth 400000`), universally in `ρ` and `κ`. Key discovery, caught by `rfl` refuting the naive statement: **the knot closures capture the initial environment inside themselves**, so the post-startup artifacts (`knotStoreF`, `metaEnvF`) are ρ-parametric *self-computing definitions* — extracted by running the machine inside the definition; store/env *spines* stay concrete, so `knot_length ρ : (knotStoreF ρ).length = 14` holds symbolically — `K₀ = 14` is now a theorem, not a count. `meval_entry`: every adequacy run reaches the canonical meval-entry state in exactly `startupSteps + 4` steps; later rungs start there and never re-cross the knot. | **[lean]** |
| 3b(ii) | `AdequacyLeaf.lean` (5 thms): **the leaf forms, universally.** Variables: adequacy over *all* indices `n : Nat` by one symbolic kernel reduction — the 144-step interpreted run never inspects the numeral (`mnth` tests the environment first), so `n` is a passenger and one `rfl` closes an infinite syntax class; both worlds miss with related defaults (rung 2's error-agreement, now a top-level universal). Atoms: all eight by `fin_cases` + native execution — the pairing `(quo . k) ~ elem k` is `eatom ∘ qatom = id` recomputed by the interpreter's tag trees. Exact fuel on the meta side via the fuel-transfer lemmas (`loop (varSteps + entrySteps)`). | **[lean]** |
| 3b(iii) | `AdequacyBeta.lean` (5 thms): **β by families** — the passenger principle reaches into compound programs: an application's dispatch skeleton (`mform` app-tag, argument order, `mapply` trees, closure entry) is concrete, so infinite families close by single kernel reductions. `adequacy_beta_var` (id on any variable, 760 interpreted vs 7 direct steps — ~110× overhead, constant across the family); `adequacy_K` (**doubly infinite**: K on any two variables, two β's, `mnth` at depth 1); `adequacy_beta_nested`; `adequacy_beta_closure` (a closure *returned through* β — `RepV.clos` on a compound run); `adequacy_beta_atom` (all eight, `fin_cases`). ~9 min of kernel reduction total. | **[lean]** |
| 3b(iv) | `AdequacySim.lean` (31 thms): **the general simulation induction** — universal adequacy for the applicative fragment (atom/var/lam/app, arbitrarily nested, every represented environment, every continuation). Probe-discovered, `rfl`-certified architecture: META's internal `meval` is the knot-cell-9 closure, curried (quotation, then environment); `mevalCall` extracts the calling convention self-computingly, and every recursive self-call re-enters it. Application is three dispatch segments (129/29/214 steps) glued by two *self-computing continuation transformers* (`appKf`/`appKx` — defined by running the machine and projecting; the `rfl`s certify their true dependencies); the apply phase is a **tail call**, so `KRempty` suffices — no continuation reasoning. `mnth` (cell 8) simulates `chainNth` by induction against the `RepEnv` derivation, its nil case the leaf rung's passenger. The magma itself fires as a *naked host application* mid-interpretation (`elem_fire`), making all 64 products one symbolic reduction. **Every error arm agrees** (elem·non-elem, cell-applied, loc-applied → `(quo.tt)` ~ `elem 0`) — §5 risk 3 discharged for this fragment, no META fix needed. Master `meval_sim` by induction on big-step `EvP` (machine-mirroring, arm for arm — `evp_steps`); corollaries `adequacy_pure`, `adequacy_product` (the interpreted magma *is* the magma, zero kernel cost), `adequacy_id_tower` (unbounded nesting depth × all indices — adequacy infinite in program **structure**, beyond any finite family of skeleton reductions). ~22 min elaboration. | **[lean]** |
| 4 | `AdequacyData.lean` (32 thms): **the data forms join the induction.** `EvD` extends the big-step relation with nine clauses mirroring the machine arm for arm — `cons`, both `car` arms, both `cdr` arms, both `pairp` arms, and all three `ite` arms (ff → else; every non-ff element *and* every non-element value → then, exactly the machine's `iteK` pair). `evP_evD` embeds rung 3b(iv)'s relation. New dispatch kit, probe-first as before: `cons` = the application pattern in miniature (223/20-step segments, two self-computing transformers, then `cons_pack` — the machine's own `consR` arms build the tagged pair in 2 symbolic steps, this rung's `elem_fire`); `car`/`cdr`/`pairp` dispatch on the result tag (64 steps for cells *and locations* — the discriminating path; 57 for elements/closures), payloads passengers; `ite`'s branch calls are all **tail calls** (119/119/114/73/73), so `KRempty` still suffices. **Every error and edge arm agrees again** (car/cdr of non-cells, pairp's no on locations, ite's truthiness on non-elements) — risk 3 stays discharged, no META fix. The master `meval_simD` re-proves nothing: its eight pure cases invoke the imported 3b(iv) kit verbatim. Store still untouched (cells are immediate values — rung 5 is where alignment engages). Corollaries: `adequacy_data` (10-form closed programs), `adequacy_list` (every quoted list — infinite in *data* structure), `adequacy_car_cons` (constructor/projector roundtrip, all 64 pairs, zero kernel cost). ~54 min elaboration; `mite_elem_tt` carries a ten-fold heartbeat budget (eight kernel reductions in one theorem). | **[lean]** |
| 5 | `AdequacyStoreKit.lean` (57 thms) + `AdequacyStore.lean` (9 thms): **the store forms join the induction — alignment engages.** The kit restates every rung-3b(iv)/4 dispatch lemma over `knotStoreF ρ₀ ++ σ'` (concrete prefix spine, symbolic suffix — each `rfl` *certifies* its segment never touches the live store; the committed transformers were already suffix-independent) and adds the store segments: `ref` = 194 dispatch steps to *concrete* frames `refK·consR[quo-tag]`, then `ref_alloc` — the machine's own `refK` arm at **any** store: the canonical map `i ↦ K₀+i` is the allocation rule meeting the knot prefix, not bookkeeping; `deref` = 193 + 63 to a **tail-position naked read** (`derefK` directly on the caller's continuation), the read arm fully symbolic; `setref` = 188/23/68 + naked write + 2-step unwind over a fully-symbolic written store. `EvS` threads stores through all 22 clauses; `meval_simS` carries rung 2's alignment as the induction invariant, with rung 2's algebra (`set_append_right'`, `forall₂_append/set`, `getD_append_right'`) doing the bookkeeping propositionally while the `rfl`s keep stores in machine-term form. **Two honest discoveries**: (a) the written value is the campaign's **first non-passenger** — META's post-write closure *captures* it, and the `rfl` refuted the dummy-extracted transformer (fix: full parameters, `setKp` takes `wT`); (b) `derefLoc` carries an in-bounds premise — out-of-bounds reads return defaults differing *in kind* (machine `elem 0` vs META's naked `elem 0` where its convention needs `(quo.tt)`) — unreachable for machine-created locations (stores only grow; `ref` allocates at the length), liftable later by a store well-formedness invariant. Store error arms all agree. Corollaries: `adequacy_store` (12-form closed programs, final stores pointwise related), `adequacy_ref_deref` (the roundtrip, all 8), `adequacy_setref` (allocate-overwrite-return, all 64). ~52 min kit + ~7 min master elaboration. | **[lean]** |
| 6 | + `callcc` absorption (the continuation relation) | [open] |
| 7 | Top theorem + tower-at-every-height corollary | [open] |

Estimate: comparable to the factorization ladder (~70+ theorems,
weeks-to-months at ladder pace). Rungs 3–6 each end difftested: the
fragment theorem's statement instantiated on corpus programs must
reproduce the observed values.

## 7. Related work anchors (for the sequel paper)

Brown–Palsberg (POPL 2016; escape the normalization barrier by typing
away the diagonalization gadget — the same escape-shape as our walls,
recorded in `docs/lawvere-diagonal-and-the-walls.md` §7);
Rendel–Ostermann–Hofer (first typed self-recognizer); Amin–Rompf
(POPL 2018; towers collapsed by staging — ours by adequacy); CakeML's
bootstrap (verified compiler self-application; different metatheory
relationship). The distinctive claim: a *deep* self-interpreter,
proved adequate, whose quotation is the machine's own certified
algebra — the theorem's statement mentions one machine and nothing
else.

## 8. File pointers

- `Magma/AdequacyTags.lean` — rung 0 **[lean]**
- `Magma/AdequacyRep.lean` — rung 2 **[lean]** (deferred from it, to
  when first needed: determinism of `RepV` given functional `KR` —
  the Fin-literal index gymnastics are not worth paying before a
  consumer exists)
- `Magma/AdequacyInstances.lean` — rung 3a **[lean]** (also deferred:
  soundness of `beqV` — the Bool run-checks suffice for regression
  armor, and the universal theorem will not pass through `beqV`)
- `Magma/AdequacyStartup.lean` — rung 3b(i) **[lean]** (technique of
  record: symbolic kernel-`rfl` through concrete step counts works at
  ~1275 steps/14 s; ρ-parametric self-computing extraction beats
  pasted terms — and `rfl` itself catches wrong statements, as it did
  the env-capture)
- `Magma/AdequacyStoreKit.lean` + `Magma/AdequacyStore.lean` — rung 5
  **[lean]** (lessons of record: map error line numbers to theorems
  *exactly* before fixing — a misread column cost a 55-minute
  rebuild aimed at the wrong lemma; kit/master file split pays for
  itself the first time a deep lemma fails; triple-nested
  transformer types need the 10× heartbeat budget; and when a
  dummy-extracted transformer is refuted by `rfl`, the value it was
  dummying is captured in the frames — parameterize, don't guess)
- `Magma/AdequacyData.lean` — rung 4 **[lean]** (the extension
  pattern of record for rungs 5–6: new `EvD` clauses arm-for-arm
  with the machine, probe → dispatch lemmas → master case per
  clause; budget note — a `fin_cases` over `Fin 8` whose cases each
  embed a transformer reduction needs ~10× heartbeats)
- `Magma/AdequacySim.lean` — rung 3b(iv) **[lean]** (techniques of
  record: right-side inversion lemmas with equation-shaped
  conclusions beat `cases` on the relation — robust under `subst`
  orientation; self-computing continuation transformers make frame
  bookkeeping `rfl`-checkable; splitting a dispatch segment at a
  naked host application turns an 8×8 case grid into one symbolic
  reduction; fuel existential at this rung — the monotone
  transformer is rung 7's)
- `Magma/MetaImage.lean` — rung 1 **[lean]** (generated; regenerate
  via `BLESS_META_IMAGE=1 cargo test -p kamea-scheme --test
  meta_image`, then copy the goldens)
- `kamea-machine/crates/kamea-scheme/tests/meta_image.rs` — the
  Rust half of the pin (+ closedness check)
- `kamea-machine/crates/kamea-scheme/src/lib.rs` — `META_CLOSED`,
  the adequacy corpus, the tower test
- `MACHINE.md` §9–10 — the ladder this campaign stands on
- `docs/lawvere-diagonal-and-the-walls.md` — why the theorem's
  self-reference is safe (the walls quarantine the diagonal)

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
| 3 | Adequacy, pure fragment: atoms, `mnth` de Bruijn walk (connects to `quote_var_succ`), β through `mapply`/`tagclo`; fuel transformer machinery; bridge table-level trees → running trees | [open] |
| 4 | + data forms (`mdata`: cons/car/cdr/pairp/ite arms) | [open] |
| 5 | + store forms (`mstore`; alignment invariant finished) | [open] |
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

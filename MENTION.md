# MENTION.md — the mention-algebra experiment

The certified law set of the N=8 kernel, tested as an **inductive
bias** in LLMs on the instruction/data-separation problem. Companion
plan document to MACHINE.md / ADEQUACY.md / PEARL.md; this one is an
ML experimental design, sized to align with the existing
instruction-data-separation literature (7B-class models).

Status: PLAN (2026-08-17). Nothing here is run yet.

---

## 1. Hypothesis

Prompt injection is a **use/mention failure**: content that should be
*mentioned* (data) gets *used* (executed as instructions). The kernel
is a certified, provably-unique algebra of use/mention: quotation
with laws (retraction, involution, self-location, closure-as-theorem)
rather than conventions. The hypothesis: enforcing fragments of this
algebra as architectural constraints in a transformer improves
instruction/data separation — especially under **nesting** and
**adaptive attack** — at no utility cost, relative to ad hoc marking
schemes.

Two fragments of the law set already pay rent in deep learning,
adopted without the theory:

- **Tied input/output embeddings** = a retraction law
  (`eval ∘ quote = id` as weight tying).
- **ASIDE** (2025): rotate data-channel token embeddings by a fixed
  orthogonal (isoclinic π/2) map, fine-tune, improve separation.
  That is a *proto-quote operator* — chosen with no theory of what
  laws a mention operator must satisfy.

The kernel supplies the missing laws, each with a certificate, and
each translating to a testable architectural delta.

## 2. The laws, translated

| Kernel law (certificate) | Architectural translation | Condition |
|---|---|---|
| Quote is an **involution** on the core (H2; `selfloc_closure.py`: without it, the two quote six-cycles break self-judgment) | The mention operator Q satisfies **Q² = I** (reflection), not order-4 rotation | C2–C4 vs C1/C5 |
| **Retraction**: eval undoes quote; in the certified table quote's and eval's rows are *identical on the core*, differing at one absorber cell (`rawA8` rows 2–3) | **E = Q**: promotion (un-quoting) is the same tied operator; one polarity bit distinguishes the direction, carried by the channel annotation | round-trip split |
| **Self-location** (A1/A3/A4, `CoreCanonical.lean`): the classifiers ARE the quotations of the operators | The mention **judge is derived from Q** (its eigenstructure), not a free head — no shadow judge with independent parameters | C3 vs C2 |
| **Closure is a theorem** of self-location + involution (`selfloc_closure.py`, UNSAT) | Judgments about mentioned content remain judgeable at every nesting depth — a consistency regularizer on nested batches | C4 |
| **Walls** (`DataWalls.lean`): structure cannot live in the algebra; depth lives in the store | Q marks the *sort* (mention vs use), applied **once**; nesting **depth is carried structurally** (content/position), never by iterating Q | C6 (negative prediction) |
| **Rigidity/canonicity** (`CoreCanonical.lean`, Aut = 1) | The package is not one design among many: the discrete ideal is unique. The experiment prices each law separately, ledger-style | the grid itself |

## 3. The mention-algebra layer (spec)

Notation: hidden size `d`; token embedding `x ∈ R^d`; every token is
annotated with a channel bit `c ∈ {use, mention}` (as in ASIDE:
instruction-channel vs data-channel), extended to nested data by the
rule in §3.4.

### 3.1 Q — the quote operator

An orthogonal involution:

    Q = U · diag(I_{d−k}, −I_k) · Uᵀ,   Q² = I by construction

- `U`: orthonormal basis, parameterized as a product of Householder
  reflections (or Cayley transform); either **fixed** (identity basis
  — negate the last k dims; the cheapest arm, exactly comparable to
  ASIDE's fixed rotation) or **learned** during fine-tuning under the
  orthogonality parameterization.
- `k = d/2` by default (mirrors ASIDE's isoclinic choice acting on
  all coordinate pairs); `k` swept in the pilot.
- Application: at the embedding layer, mention-channel tokens get
  `x ← Q x`. Use-channel tokens pass through. (Per-layer application
  is an extension arm, not the base spec.)

### 3.2 E — the retraction (promotion path)

`E := Q` (tied; an involution is its own inverse). Authorized
promotion — "follow the instructions in the document below" — is the
*same operator* applied under a use-channel annotation, plus the
polarity bit from the annotation itself. No separate un-marking
machinery exists or is trained. This mirrors the certified table,
where eval's core action *is* quote's.

### 3.3 The self-located judge

The judge decides, per token/span, whether content is currently
mention or use. It has **no independent parameters**:

    s(x) = ⟨ x, (I − Q) μ ⟩

where `μ` is the running mean embedding over the training corpus
(a buffer, not a parameter). `(I − Q)μ = 2 μ₋` is the component Q
flips; marked tokens have it negated, so `sign(s)` reads the sort
directly off Q's eigenstructure. The judge is *the quotation map
looked at as a classifier* — self-location as parameter tying.
(Free-head ablation C2 replaces this with a trained linear probe of
equal output dimension.)

The judge is used two ways: (a) as an auxiliary token-level channel
prediction whose loss trains representations to keep the sort
legible; (b) at evaluation, as the attack surface for the adaptive
red-team comparison (§5.5).

### 3.4 Closure regularizer and the depth rule

**Depth rule** (from the walls): Q is applied exactly once to any
mention-channel token, regardless of nesting depth. A document
quoting a document is still *mention* — a sort, not a counter. Depth
is represented structurally (the content's own quoting syntax,
position, and context), never by iterating Q. Condition C6
implements the "obvious" wrong generalization (apply Q per nesting
level) to test the prediction that it degrades at depth ≥ 2 — the
architectural analogue of the six-cycle countermodels.

**Closure loss** `L_clo`: on nested batches (§5.2), the tied judge's
channel prediction must be correct at every depth, and the model's
behavioral target is standard SFT (never execute probes at any
depth). `L = L_SFT + λ_judge · L_judge + λ_clo · L_clo`, with
λ swept in the pilot.

## 4. Models and training

Aligned with the ASIDE literature so numbers are comparable:

- **Primary (7B-class)**: Llama-3.1-8B and Qwen2.5-7B (two families;
  base models, not instruct, matching ASIDE's protocol).
- **Pilot (1B-class)**: Llama-3.2-1B and Qwen2.5-0.5B for the full
  grid and hyperparameter sweeps before any 7B spend.
- **Recipe**: reproduce ASIDE's released SFT setup (instruction-
  tuning corpus with instruction/data channel annotations, plus
  probe-injection augmentations), identical data and schedule across
  all conditions; full fine-tune at 7B for headline conditions, LoRA
  permitted for pilot-grid arms. Round-trip (promotion) training
  items (§5.3) are added to **all** arms equally, so the tying
  advantage — not data access — is what is measured.
- Phase 0 reproduces ASIDE's published numbers before anything else;
  if the reproduction fails, stop and debug — nothing downstream is
  interpretable without it.

## 5. Evaluation suite

1. **SEP** (separation score; primary, literature-comparable).
2. **Nested-SEP** (new; released as an artifact of this project):
   each SEP item wrapped in k ∈ {1, 2, 3} levels of realistic
   quoting contexts (document-quoting-document, email chains,
   JSON-in-markdown, "review this transcript in which..."), probe at
   the innermost level; metric = separation score as a function of
   depth. Generation is mechanical from SEP items; generator script
   committed with fixed seeds.
3. **Round-trip split** (new): SEP-derived items where the
   instruction channel *explicitly authorizes* executing the data
   content; correct behavior is promotion (execute). Metrics:
   promotion accuracy, and separation on matched unauthorized
   controls (no collateral damage).
4. **Injection robustness**: BIPIA (indirect prompt injection) and a
   TensorTrust/CyberSecEval-injection subset — matching whichever of
   these ASIDE reported, confirmed against their code in Phase 0.
5. **Adaptive attack on the judge**: suffixes optimized (GCG-style
   plus manual red-team) to flip the judge without changing content
   semantics. Comparison: free head (C2) vs tied judge (C3). Metric:
   attack success rate against the judge, and whether judge-fooling
   transfers to behavior-fooling.
6. **Utility controls**: IFEval, MMLU (5-shot), AlpacaEval-2
   (length-controlled) — all arms must be within noise of C0.

## 6. Conditions (the ablation grid — ledger discipline)

| # | Condition | What it prices |
|---|---|---|
| C0 | vanilla SFT, no marking | floor |
| C1 | ASIDE: fixed isoclinic π/2 rotation | the literature baseline; order-4 marking |
| C2 | involution Q, free judge head | the involution law alone |
| C3 | involution Q + tied (self-located) judge | + self-location |
| C4 | C3 + closure regularizer | the full package |
| C5 | random fixed orthogonal map (generic order) | "any marking helps" control |
| C6 | involution applied per nesting level | the predicted-wrong generalization |
| C7 (optional) | StruQ-style delimiter tokens | marking as vocabulary, not geometry |

Pilot: full grid × 2 families × 3 seeds at 1B. Promotion to 7B:
C0, C1, C3, C4, C6 × 2 seeds × 1–2 families, informed by the pilot.

## 7. Registered predictions

- **P1**: C3/C4 ≥ C1 on plain SEP (parity acceptable — SEP may
  saturate at 7B); strictly better on Nested-SEP with the gap
  growing in depth k.
- **P2**: involution arms learn the round-trip (promotion) split with
  higher accuracy and less data than C1/C5 given identical training
  items — because promotion shares weights with demotion (E = Q).
- **P3**: adaptive attacks that fool the free judge (C2) without
  changing behavior exist; the tied judge (C3) cannot be fooled
  independently of the mechanism — a measurable gap in judge-attack
  success and in its transfer to behavior.
- **P4**: C6 underperforms C3 at depth ≥ 2 (the six-cycle lesson:
  iterated marking loses the sort).
- **P5**: all marking arms within noise of C0 on utility.

Any prediction failing is reported as a negative result with the
grid; the design is publishable either way, and the grid *is* the
methodological contribution: every law priced separately, in models,
the way `ablate_ledger.py` priced them in the algebra.

## 8. Compute budget (rough)

- Pilot grid: 8 conditions × 2 families × 3 seeds at ≤1B, LoRA,
  short schedule ≈ 50–100 A100-hours total.
- 7B promotion: 5 conditions × 2 seeds × full SFT (ASIDE-scale
  data, 1–3 epochs) ≈ 60–120 A100-hours per run → ~600–1,200
  A100-hours; ~half that if one family carries the headline and the
  second family spot-checks C0/C1/C4.
- Evaluation: negligible next to training.

## 9. Risks, stated honestly

- **Geometry risk**: pretrained embedding spaces may not cooperate
  with a *fixed-basis* involution (the identity-basis arm); the
  learned-basis parameterization is the mitigation, and the pilot
  decides.
- **Saturation risk**: plain SEP may cease to discriminate at 7B
  with channel-annotated SFT; Nested-SEP and the adaptive-attack
  eval are the designed headroom.
- **Mapping risk** (the biggest): the theory's discrete laws
  license *structure*, not gradient-descent gains. The depth rule
  (§3.4) is the riskiest translation — the kernel carries depth in
  the store, and "structural depth" in a transformer is an
  interpretive choice. C6 exists to make this a measurement instead
  of an assumption.
- **Reproduction risk**: Phase 0 gates everything.

## 10. Phases

- **Phase 0** — reproduce ASIDE at 1B and 7B (one model), confirm
  benchmark suite from their released code. Gate.
- **Phase 1** — pilot grid at 1B; λ and k sweeps; freeze the spec.
- **Phase 2** — 7B promotion runs; evaluation; analysis scripts with
  committed asserts (the repo's discipline).
- **Phase 3** — writeup. Framing: "an ad hoc defense family, given
  its missing algebra — with certificates"; the kernel repo is the
  theory citation, not the venue (this is an ML systems/security
  paper, separate from the LMCS/ICFP pair).

## 11. Companion experiment (optional appendix)

The contamination-free in-context-semantics probe: the kernel
language's complete spec (8×8 table + 13 forms) fits in a prompt;
the certified machine grades exactly; the adequacy theorem supplies
matched run-vs-interpret task pairs. Zero training-set contamination
is possible by construction. Cheap (inference-only), and it measures
whether the *same models* that benefit from the mention layer can
acquire the full algebra in context — a link between the bias story
and the instrumentation story.

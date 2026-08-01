# The Second Write-up: "Metacircularity as a Theorem"

**Status**: DRAFTED, 2026-07-24 — `pearl/main.tex` (acmart, ~700
lines; compiles with any TeX Live that has acmart; no TeX on this
machine, so the draft is structurally linted but not yet compiled).
The draft covers everything below plus what landed after this
proposal was written: the data rung (certified homoiconicity), the
Rust host with differential pinning (24k cases), the surface Lisp
(letrec-as-knot, syntax-rules, extensionality-as-eqv?), and the
metacircular evaluator with the adequacy corpus and the two-level
tower — which serves as the closing section. Axiom footprint checked
via `#print axioms`: the **ladder's 98 theorems use propext only**
(no Classical.choice, no Quot.sound) — the abstract's claim is scoped
to the ladder and is exact. Repo-wide the trust base is stratified
(completeness wall: no axioms at all; frame-derivation and structure
theorems: classical choice via Mathlib's finiteness machinery; N=10
enumeration witnesses: `native_decide`, i.e. compiler trust); §7 of
the draft states this precisely — do not claim propext-only for the
whole repo. Remaining: one polish pass, venue formatting (currently
`acmsmall,review`).

Original proposal below, kept for the planning record. Companion
docs: `MACHINE.md` (architecture, why each rung exists), `CLONES.md`
(the algebra-side calling card — different audience, do not merge
the two).

---

## 1. The pitch

Every Lisp rests on one law: `(eval (quote p))` is `p`, run. R7RS
§6.12 stipulates it, every implementation implements it, textbook
metacircular evaluators exhibit it — but nowhere is it *derived*. This
pearl presents a small language in which the metacircular law is a
**theorem**: a corollary of an independently certified eight-element
algebra, with the proof's base case discharged by a single `decide`
against a Cayley table. The machine is then rebuilt four times —
environments, closures, first-class continuations, a mutable store,
ending at full CESK — and the law survives every restructuring with
the same base case. The machine is repeatedly swapped out from under
the law; the law keeps holding onto the same eight-element fact.

One sentence for the abstract's spine: *we keep changing the machine;
the law keeps being the same theorem about the same table.*

## 2. Genre and venue

- **Primary: ICFP functional pearl.** The shape fits the genre
  exactly: one idea, an elegant artifact, a narrative that builds, no
  literature-survey burden. Pearls are judged on polish and delight.
- Alternates: JFP (pearl track, no deadline pressure), Scheme and
  Functional Programming Workshop (the single most sympathetic
  audience on earth for "where does quote come from"; good for a trial
  run of the talk), CPP/ITP (only if reframed as a formalization
  paper — weaker fit, the mechanization is easy by ITP standards; the
  *idea* is the contribution).
- Anti-recommendation: do not aim this at a universal algebra venue,
  and do not make the main paper carry it. Different audiences,
  different currencies.

## 3. Audience contract

PL people. Assume: they know CEK/CESK, call/cc, de Bruijn, Reynolds,
Danvy. Do not assume: any universal algebra. The algebra enters the
pearl as a *found object*: a frozen 8×8 table with two absorbers and
five certified laws, plus a two-sentence story of where it came from
(law set → SAT enumeration → 228 tables → lex-min; "derived, not
designed") and one-sentence statements of the two walls to motivate
the two-level architecture. Everything deeper points to the main
paper. The pearl needs only:

- `eatom_qatom` (the retraction law — THE base case),
- the duality pairing (each operator's code is its judge — for the
  self-application demo),
- the walls (K-infinity → external loop; pairing/recognizer walls →
  tags live on the tape; sort-collapse → user quote is driver-level).

## 4. Narrative arc (proposed sections)

1. **The law everyone assumes.** R7RS §6.12. McCarthy's eval. The
   observation that metacircularity is always *stipulated* — the
   evaluator defines the law it satisfies. Question: could it be a
   consequence of something smaller than an evaluator?
2. **An algebra with quote and eval inside it.** The table, the eight
   instructions, `eval·(quote·x) = x` on the core as a certified law
   of a finite structure. Two walls in two sentences: no finite table
   has a K combinator (so iteration lives in an external driver), and
   collapse-to-data quotation excludes internal eval (so user-level
   quote/eval are driver operations *underwritten by* the table's
   internal pair). The two-level architecture is forced, and the pearl
   inherits it as its design.
3. **Rung 0 — the minimal driver** (`Factorization.lean`). Atoms +
   application; the driver's only semantic step is one table lookup;
   `decode_quote` by structural induction; base case = the table.
   First statement of `eval_quote`.
4. **Rung 1 — environments** (`FactorizationEnv.lean`). R7RS eval's
   *actual* two-argument signature. The load-bearing observation:
   **representation adequacy is static** — decode never sees ρ — so
   the law is uniform in the environment.
5. **Rung 2 — closures** (`FactorizationClos.lean`). β ends totality;
   fuel; the law strengthens to *uniform in fuel* — eval∘quote and
   the program converge together, diverge together. Ω certified
   divergent. Fuel proved operational-not-semantic (`run_mono`).
6. **Rung 3 — control** (`FactorizationCtrl.lean`). The machine
   becomes System L: four `rfl` theorems (`step_halt`, `step_mu`,
   `step_throw`, `step_beta` — proper tail calls as machine shape).
   The escape-through-quotation demo. The big-step→machine simulation
   (`machine_sim`), continuation-polymorphic.
7. **Rung 4 — store** (`FactorizationStore.lean`). CESK complete. E
   captured vs S threaded, certified as a computation
   (`eval_quote_mutation`); continuations don't restore the store as
   one `rfl` (`step_throw`); conservativity upgraded to a lockstep
   bisimulation (`step_embed`/`runM_embed` — values and divergence in
   one `Option.map` equation).
8. **The punchline table.** Five machines, one law, one base case.
   A 5-row table: rung / machine / statement of `eval_quote` / what
   changed / what didn't (the base case — never).
9. **The honest seam.** What the algebra forces vs what we chose
   (see §6 below). This section is what makes the pearl trustworthy
   instead of grandiose; write it with the same discipline the clone
   reviews imposed.
10. **Related work** (short, pearls keep this light): Reynolds
    definitional interpreters; Danvy's functional correspondence (our
    ladder is its certified cousin); Curien–Herbelin λ̄μμ̃; verified
    Lisps/Schemes — Milawa, Jitawa, CakeML — with the key contrast:
    *they verify an implementation against a stipulated semantics; here
    the semantics' defining law is itself derived from a smaller
    certified object.* McCarthy 1960, obviously.

## 5. The exhibits (all already proved; file pointers)

| Exhibit | Theorem | File |
|---|---|---|
| The base case | `eatom_qatom` | `Factorization.lean` |
| The law, ×5 | `eval_quote` (each rung) | all five |
| Adequacy is static | `decode_quote` (no ρ, no fuel, no σ) | Env/Clos/Ctrl/Store |
| Converge/diverge together | fuel-uniform `eval_quote` + `Omega_diverges` | `FactorizationClos.lean` |
| Duality reached by β | `eval_quote_duality_demo` ((λx. x·x) quote ⇒ data?) | `FactorizationClos.lean` |
| System L as `rfl` | `step_halt/mu/throw/beta` | `FactorizationCtrl.lean` |
| Escape through quotation | `eval_quote_callcc_escape` | `FactorizationCtrl.lean` |
| Big-step→machine | `machine_sim` | `FactorizationCtrl.lean` |
| Ω as a finite cycle | `machine_delta_cycle` (5 states) | `FactorizationCtrl.lean` |
| E captured, S threaded | `eval_quote_mutation` | `FactorizationStore.lean` |
| call/cc doesn't restore σ | `step_throw` (store version) | `FactorizationStore.lean` |
| Lockstep conservativity | `step_embed` → `runM_embed` | `FactorizationStore.lean` |
| Conservativity, every rung | `run_embed`/`eval_quote_embed`/`machine_embed` | each rung |

The artifact for artifact evaluation is the repo itself: `lake build`,
31 files, ~362 theorems, zero `sorry`, pinned toolchain.

## 6. The honest-claims ledger (hold this line)

**Theorems (claim freely):** the atomic quote/eval duality and its
retraction law; the necessity of the two-level architecture (walls);
the necessity of heap tags (recognizer wall); the forced negation law
of introspection; the external driver loop and hence real divergence;
metacircularity as a corollary at every rung; conservativity of every
extension.

**Engineering (label as such, always):** tag *values* (which element
marks λ vs app vs var vs μ vs store forms); the compound encoding;
numerals; frame layouts; which value `setref` returns. The compound
layer above the atoms is standard PL metatheory, cleanly done — its
connection to the algebra is through the atoms and the walls, not
through every constructor.

**The "first" claim, exact phrasing:** "We know of no other system in
which the eval/quote law of a running language is a *consequence* of
an independently certified structure, rather than a property stipulated
by (or verified against) the language's own semantics." Contrast with
verified Lisps explicitly; invite counterexamples.

## 7. Work remaining (prose only — no new Lean strictly needed)

- Write it: ~12–20 pearl pages. Estimate 3–5 focused days of writing.
- Figures: the ladder diagram (5 rungs, arrows = conservativity, one
  dashed line down to `eatom_qatom`); the 8×8 table with role labels;
  the punchline table of §4.8.
- Optional Lean garnish (nice, not necessary): a quasiquote/unquote
  pair at the driver level; the machine→big-step completeness
  direction on the control rung (currently one-directional + lockstep
  at the store rung, which suffices); a `dynamic-wind` sketch. Do NOT
  block the paper on any of these.
- Naming pass: the paper should name the language. Candidate: **Kamea**
  (already the project's word for the artifact) — "the Kamea machine."
- Decide author-voice question: the pearl reads best written plainly in
  first person plural with zero grandiosity; let the theorems be loud
  and the prose quiet.

## 8. Title candidates + abstract seed

Titles, roughly in order of current preference:

1. *Metacircularity as a Theorem*
2. *eval (quote p) = run p, Derived*
3. *The Quotation Is the Proof*
4. *Where Does Lisp Come From?* (keep as a section title instead;
   too cheeky for the masthead)
5. *One Law, Five Machines: Certified Metacircularity from an
   Eight-Element Algebra*

Abstract seed (compress to ~150 words at writing time):

> Every Lisp stipulates that evaluating a quotation recovers the
> program: `(eval (quote p))` behaves as `p`. We present a small
> language in which this law is a theorem. Its quote and eval are
> underwritten by an eight-element algebra — itself derived by
> enumerating a law set and taking the lexicographically minimal
> model — whose certified retraction law becomes the base case of the
> metacircularity proof. We then rebuild the evaluator four times:
> adding environments, closures, first-class continuations, and a
> mutable store, ending in a call-by-value sequent-calculus (CESK)
> machine with proper tail calls as machine shape. Each extension is
> proved conservative over the last, and the metacircular law survives
> every restructuring unchanged, uniformly in fuel — programs and
> their quotations converge together, diverge together, and agree on
> every value. All results are mechanized in Lean 4 with zero axioms
> beyond the kernel [check phrasing] and zero `sorry`.

## 9. File pointers

- The ladder: `Magma/Factorization.lean` → `FactorizationEnv.lean` →
  `FactorizationClos.lean` → `FactorizationCtrl.lean` →
  `FactorizationStore.lean`
- The table and its laws: `Magma/ArtifactN8.lean`
- The walls: `Magma/CompletenessWall.lean`; sorting/collapse:
  `Magma/Sorting.lean`; introspection: `Magma/Homoiconic.lean`
- Architecture rationale: `MACHINE.md` (§3 correspondence table is
  the seed of the pearl's §6 rung; §9 item 1 records the ladder)
- Main paper (the algebra story, cite as companion): `paper/main.tex`

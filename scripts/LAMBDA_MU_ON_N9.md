# λμμ̃-on-N=9: σ-symmetric execution prototype

**Status:** working prototype. ~400 lines. See `psi_lambda_mu_n9.py`.

## What this is

The N=9 canonical-witness substrate has algebra-level involution σ = (f η)(Q E).
Earlier experiments showed σ is a real symmetry of the *Cayley table* but not of
plain λ-calculus over the substrate — the eval rules for Q (lazy) and E (eager)
are asymmetric, and Vars only make sense under Q-binders. An empirical zoo
showed σ-images of *combinators* are engineering-meaningful (multi-prompt
selectors, CPS pair eliminators) while σ-images of *user programs* are
well-typed gibberish.

This prototype tests the Curien-Herbelin λμμ̃ reading of the substrate:

| N=9 atom | λμμ̃ role |
|---|---|
| Q | λ — value-side binder |
| E | μ̃ — continuation-side binder |
| g | cut packaging (value, continuation) |
| f | extract value-half of cut |
| η | extract continuation-half of cut |

Two AST extensions are added: `CoVar(k)` (de Bruijn co-variable) and `CoLam(body)`
(continuation binder). An extended involution σ̂ swaps `Var ↔ CoVar` and
`Lam ↔ CoLam` in addition to the algebra σ. β-reduction and μ̃-reduction are
both rules of the cut-form `App(E, App(App(g, M), N))`; which fires depends on
what's on each side of the cut.

## What works

**(a) The engineering-meaningful case — K and σ̂(K) both implement "first projection," on dual data.**

```
K        = Lam(Lam(Var(1)))         -- λx. λy. x   (returns first of two VALUES)
σ̂(K)     = CoLam(CoLam(CoVar(1)))   -- μ̃α. μ̃β. α  (sends value to first of two CONTINUATIONS)

⟨⟨K | T⟩ | NIL⟩         → T   -- K picks the first value
⟨NIL | ⟨T | σ̂(K)⟩⟩      → T   -- σ̂(K) picks the first continuation
```

K runs by β-reductions extending the value environment; σ̂(K) runs by μ̃-reductions
extending the continuation environment; both compute the same logical operation
on dual data structures. **The substrate's σ does land on the polarity involution
of λμμ̃, made operational.**

This is exactly the construct used in shift/reset, Racket's `racket/control`, and
multi-prompt delimited continuations.

## What doesn't

**(b) Factorial — σ̂(fact) is well-typed gibberish, as predicted.**

Factorial runs correctly in the λμμ̃ encoding:
```
fact(0..6) = 1, 1, 2, 6, 24, 120, 720
```

σ̂(fact) is a closed AST term. We can apply σ̂ structurally to every node, get back
something well-typed, and run it. But:

- `σ̂(nat(3))` = `App(E, App(E, App(E, T)))` reduces to z₁ (a single atom!) via
  the E-on-atom dot fallback. **There are no "co-naturals"** — Q-chains dualize
  to E-chains that just fold via the table.
- The Prim escape hatches (`mul`, `sub`, `zero?`) have no continuation-side
  duals. σ̂ passes them through unchanged but the resulting "co-mul" has no
  semantics.
- Even with those filled in, the σ̂-image of arithmetic recursion is a
  co-recursive continuation program — an anamorphism on the continuation side,
  not a program anyone needs computed.

Confirmed: σ̂ runs structurally but produces gibberish. **σ̂-equivariance does
not give proof reuse on value-recursive programs**, exactly as the empirical
zoo predicted before the build.

## Sharp finding from the build

Even on the cleanest case — `App(f, pair(T, NIL))` — eval doesn't commute with σ̂:

```
P        = App(f, pair(T, NIL))   → T    (6 steps)
σ̂(P)     = App(η, pair(T, NIL))   → NIL  (6 steps)
σ̂(nf(P)) = T   ≠   nf(σ̂(P)) = NIL
```

Step counts match, but the operations return different elements. The reason:
**fst and snd are absolute positions in a pair, not σ-permutable concepts.**
σ swaps the *atoms* f and η, but pair `(z₂, z₁)` really does have z₂ in slot 0
and z₁ in slot 1 — the answer to "which slot is first" is absolute. σ swapping
the projection atoms gives a different operation on the same data, not the
dual operation on dual data.

This is the same structural reason σ-symmetric execution holds for K (whose
"first" is environment depth, σ-permutable) but fails for f-on-pairs.

## Diagnostic 1 — Is σ̂ computable on closed AST terms?

**Yes.** σ̂ is a finite structural recursion:

```
σ̂(int n)              = SIGMA[n]                              -- algebra σ
σ̂(App(f, a))          = App(σ̂(f), σ̂(a))
σ̂(Var(k))             = CoVar(k)
σ̂(CoVar(k))           = Var(k)
σ̂(Lam(body))          = CoLam(σ̂(body))
σ̂(CoLam(body))        = Lam(σ̂(body))
σ̂(Closure(b, V, K))   = CoClosure(σ̂(b), σ̂(K), σ̂(V))    -- venv ↔ kenv
σ̂(CoClosure(b, V, K)) = Closure(σ̂(b),  σ̂(K), σ̂(V))
σ̂(Prim(name, args))   = Prim(name, σ̂(args))             -- pass-through
```

No oracle needed. O(|term|) on any closed AST. The Prim case is the one place
where σ̂ is silently incomplete — it doesn't generate dual primitives, it just
preserves the names. For full σ̂-equivariance on Prim-bearing programs you'd
need to also dualize the primitives table, which is a separate (and probably
unrewarding) exercise.

## Diagnostic 2 — Does the substrate's polarity match WispyScheme's CPS conventions?

**Yes — perfect match.** WispyScheme's `examples/rsc.scm` already maintains the
polarity distinction at the AST level:

| WispyScheme rsc.scm | N=9 substrate |
|---|---|
| `lam`       (user value-binder)        | `Lam`, encoded by atom `Q` |
| `cont`      (CPS continuation binder)  | `CoLam`, encoded by atom `E` |
| `closure`   (closed user lambda)       | `Closure` |
| `cont-closure` (closed continuation)   | `CoClosure` |
| `*lambdas*` (collected user lambdas)   | Lams in the term tree |
| `*cont-lambdas*` (collected conts)     | CoLams in the term tree |
| `add-lambda!` / `add-cont!`            | (parallel collection) |
| `app` after CPS (every call tail)      | cut `App(E, App(App(g, M), K))` |

The substrate's σ = (Q E) names exactly the swap WispyScheme already maintains
operationally. Q is the value-binder atom; E is the continuation-binder atom.
The CPS-converted `app` form corresponds to our cut form.

**Most interesting structural finding:** the substrate gives an *algebraic* name
to a polarity distinction WispyScheme already maintains *operationally*. It
isn't that the substrate "supports" CPS — it's that the substrate's involution
*is* the value/continuation polarity that the rsc.scm pipeline already separates.
A future WispyScheme P3 over the substrate could read its CPS AST directly as
λμμ̃ terms; the σ̂ involution would then *be* the value↔continuation swap that
the existing `lam`/`cont` distinction implements by hand.

## What this buys (honest)

| Claim | Status |
|---|---|
| σ-symmetric execution exists on N=9 | ✓ on combinators (K, KI, identity, cons-builder) |
| σ̂ is computable on closed AST | ✓ structural recursion, no oracle |
| Substrate names the polarity WispyScheme uses | ✓ exact alignment with rsc.scm |
| Proof reuse for arbitrary programs | ✗ — not for value-recursive programs (factorial) |
| Bonus identities (Q²=Q, etc.) load-bear | ✗ — still atom-only, don't fire in eval |
| Removes need for dual primitives | ✗ — Prims pass through σ̂ unchanged, no semantics |

The substrate has earned its keep as **the algebraic ground for a CPS-aware /
continuation-aware Lisp**. It does NOT earn its keep as a foundation for plain
value-recursion proof reuse. For WispyScheme specifically — which already has
a CPS pipeline distinguishing `lam`/`cont` and is planning full continuations —
the substrate's σ would name a distinction the codebase already maintains.

## What's left

If WispyScheme commits to the substrate as its algebraic ground, the next steps
would be:

1. **Polarity-neutral cut form.** Currently `cut(M, N) = App(E, pair(M, N))` is
   itself polarity-laden (E on the outside). σ̂ of a complete program produces
   a Q-wrapped frozen value that doesn't reduce. The fix is to commit to a
   neutral cut shape (probably `App(App(g, M), N)` directly, with the dispatch
   trigger being structural pair-matching). Small evaluator change; makes σ̂
   close on whole programs.

2. **Dual primitives.** If `mul`, `sub`, `zero?` get continuation-side duals,
   σ̂-equivariance extends to arithmetic-bearing programs. Probably not worth
   it — the duals aren't programs anyone writes — but it's the missing piece
   if you want full σ̂-completeness.

3. **Empirical sanity on rsc.scm output.** Take a small CPS-converted program
   from rsc.scm, translate to our encoding, run, σ̂, run dual. The vocabulary
   alignment claim is structural; a one-program empirical check would confirm
   the operational alignment too.

None of these are blocking for shipping the substrate as "the algebraic ground
of WispyScheme's polarity distinction." That story is complete as of this
prototype.

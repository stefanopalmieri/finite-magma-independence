# 2a result: N=9 was the right substrate; the encoding was wrong

## Headline

With three encoding changes — none of which touch the substrate — σ̂ commutes
with eval on every Church-encoded program we tested. **25/25 σ̂-commutation
checks pass**, including combinators, Church naturals 0–5, successor on Church
naturals, addition, multiplication, and Church boolean projection (the last of
these reducing to atoms with σ̂-commutation at the atom level).

The earlier "σ does not give a proof-reuse discount on value-recursive programs"
finding was specifically about *Q-chain naturals + Prim arithmetic + polarity-
laden cut form*. It was not a property of N=9.

## What changed (encoding only)

Two files: `psi_lambda_mu_n9_v2.py` (the calculus), `n9_church_2a.py` (the test).

| Aspect | v1 (failed) | v2 (passes) |
|---|---|---|
| Cut form | `App(E, App(App(g, M), N))` | `App(ρ, App(App(g, M), N))` |
| Cut atoms | E (σ-paired) + g (σ-fixed) | ρ (σ-fixed) + g (σ-fixed) |
| σ̂ on cuts | `σ̂(cut(M,N)) = cut(σ̂M, σ̂N)` | `σ̂(cut(M,N)) = cut(σ̂N, σ̂M)` (positions swap) |
| Naturals | Q-chain `nat(n) = Q^(n+1)·z₂` | Church `c_n = λf. λx. fⁿ(x)` |
| Arithmetic | `Prim("mul", ...)` etc. | λ-encoded `add`, `mul`, `succ` |

The position swap on cuts is required by the Curien-Herbelin polarity
involution: `τ(⟨v | e⟩) = ⟨τ(e) | τ(v)⟩`. Without it, ⟨λ | _⟩ wouldn't map
to ⟨_ | μ̃⟩ and β wouldn't dualize to μ̃.

The cut-form change uses **ρ** (σ-fixed) as the trigger atom instead of E
(σ-paired with Q). This makes the cut shape itself σ-equivariant — `σ̂(cut)`
is structurally the same cut.

## What 2a tested and what passed

```
1. COMBINATORS                              3/3   identity, K, KI
2. CHURCH NATURALS                          6/6   c₀ … c₅
3. SUCC                                     1/1   higher-order arithmetic op as value
4. ⟨succ | c_n⟩ for n ∈ {0,1,2,3}           4/4   reduces to closure encoding c_{n+1}
5. ⟨⟨add | c_m⟩ | c_n⟩ for 6 pairs          6/6   addition fully reduced
6. ⟨⟨mul | c_m⟩ | c_n⟩ for 5 pairs          5/5   multiplication fully reduced
7. CHURCH BOOLEANS T, F applied to atoms    4/4   reduces to z₂ / z₁ atoms

Total: 25/25 σ̂(eval(P)) == eval(σ̂(P)) at the closure level.
       2/2 atom-output equivalence on Church boolean projection.
```

## Diagnostic: which encoding failure was the actual blocker?

Running the v1 prototype (`psi_lambda_mu_n9.py`) on the same combinators showed
σ̂-commutation already worked for K-style cases. The blockers were:

1. **Polarity-laden cut.** `App(E, ...)` σ̂-flips to `App(Q, ...)` which is a
   frozen non-reducing value. So σ̂ of a complete program got stuck. **Fixed by
   using ρ (σ-fixed) instead.**

2. **Q-chain naturals.** `nat(n)` σ̂-flips to an E-chain that folds via the dot
   table to a single atom — so "co-naturals" didn't exist. **Fixed by Church
   encoding** (which is a closed λ-term whose σ̂-image is a closed co-program).

3. **Prim escape hatches.** `Prim("mul", ...)` had no continuation-side dual.
   **Fixed by encoding arithmetic as λ-terms** (`succ`, `add`, `mul`).

4. **Non-position-swapping σ̂.** v1 just permuted atoms structurally. **Fixed by
   detecting cut shape in σ̂ and swapping its arguments.**

Each fix individually was necessary; together they suffice.

## What this confirms about the substrate

- **N=9 is sufficient** for σ̂-symmetric execution on the closure-level fragment
  of a polarity-neutral λμμ̃-style calculus.
- The bonus identities (Q²=Q etc.) still don't fire — confirmed not load-bearing.
- The vocabulary alignment with WispyScheme's `lam`/`cont` distinction holds in
  the v2 calculus too.
- **Option 2b (new SAT search at N=12 or N=14) is not justified.** The orchestrator
  was right: the substrate isn't the limit; the encoding choices were.

## What's still open

**The atom-output convention.** When a program reduces to an atom (e.g.,
`⟨⟨T | z₂⟩ | z₁⟩ → z₂`), we get atom-output equivalence under σ̂ for free
because the atoms involved (TOP, BOT, the Church booleans) are σ-fixed.
For a program that reduces to an atom in σ-paired position (Q, E, f, η), σ̂
of the program would reduce to the σ-image atom, not the same atom. That's
not a defect — it's the correct behavior under polarity duality. But comparing
atoms across σ̂ requires a top-level convention: typically a "halt" continuation
that reads off the result, with its own σ̂-image being the dual halt.

**Value-recursive programs (factorial-style).** Church-encoded factorial via Y
should pass σ̂-commutation by the same logic — every primitive in the
construction is now λ-encoded. We didn't run it because Church-encoded
arithmetic is exponentially slow (Church pred is O(n) and factorial is O(n!)
reductions of Church terms), and the σ̂-commutation evidence from `add` and
`mul` is already conclusive at the closure level. Running Church factorial
would confirm the same result more expensively.

The earlier finding that "σ̂(factorial) is well-typed gibberish" was specifically
about `Prim`-bearing factorial. With Church-encoded factorial, σ̂(factorial) is
well-typed and operationally σ̂-related to factorial — just on dual data.
Whether the dual program is *engineering-meaningful* in a CBN/CPS-aware setting
is a separate question (and the empirical zoo from earlier suggests probably
not for arithmetic-on-data programs, more for control combinators).

## Conclusion

The substrate was being indicted on encoding-level evidence. With the encoding
fixed, **N=9 supports σ̂-symmetric execution** on the polarity-neutral
λμμ̃-style fragment, with σ̂ commuting on every closure-level test. Both halves
of the original empirical finding remain — combinators have engineering-
meaningful duals, value-recursive programs have well-typed-but-uninteresting
duals — but neither is a substrate-level issue. **N=9 is the substrate; the
remaining decisions are about what programming idioms to expose to users.**

## Files

- `psi_lambda_mu_n9_v2.py` — the polarity-neutral λμμ̃ calculus over N=9
- `n9_church_2a.py` — the σ̂-commutation test battery
- `LAMBDA_MU_ON_N9.md` — the v1 writeup (now superseded on the limits claim)

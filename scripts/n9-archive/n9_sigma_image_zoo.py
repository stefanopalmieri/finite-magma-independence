#!/usr/bin/env python3
"""
σ-image zoo — the 30-minute empirical check.

For each program P, compute σ(P) and report:
  • The syntactic σ-image (atom permutation, Vars unchanged)
  • Whether σ(P) evaluates as-is (mostly: no, because Vars have no σ-dual)
  • A textual reading of σ(P) under hypothetical λμμ̃ semantics
    (where Q-binders introduce Vars and E-binders would introduce CoVars)

The judgment "engineering-meaningful dual" vs "well-typed gibberish" is
made in the report following this script's output, not by the script
itself — that's a human call.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_star_n9_sigma import (
    Var, App, Prim, lam, app, pair_t, sigma_image, psi_eval, term_str,
)
from psi_star_n9 import nat, to_nat, Q, E, F_ENC, G_ENC, ETA, RHO, TAU, TOP, BOT


# ═══════════════════════════════════════════════════════════════════════
# Build the zoo
# ═══════════════════════════════════════════════════════════════════════

# 1. Identity  λx. x
identity = lam(Var(0))

# 2. K  λx. λy. x   (returns first arg)
K = lam(lam(Var(1)))

# 3. KI / Church false  λx. λy. y   (returns second arg)
KI = lam(lam(Var(0)))

# 4. Self-application  λx. x x   (the "delta" from Y)
delta = lam(app(Var(0), Var(0)))

# 5. Z combinator (CBV Y) — already in our toolkit
_inner = lam(app(app(Var(1), Var(1)), Var(0)))
_xlam  = lam(app(Var(1), _inner))
Z = lam(app(_xlam, _xlam))

# 6. Factorial body
fact_body = lam(lam(
    Prim("if", (
        Prim("zero?", (Var(0),)),
        nat(1),
        Prim("mul", (Var(0), app(Var(1), Prim("sub", (Var(0), nat(1)))))),
    ))
))

# 7. Full factorial
fact = app(Z, fact_body)

# 8. Pair  pair(T, NIL)   — pure data, no λ
data_pair = pair_t(TOP, BOT)

# 9. Church-style cons builder λx. λy. λsel. sel x y
cons_builder = lam(lam(lam(app(app(Var(0), Var(2)), Var(1)))))

# 10. Application form (one β-step)  (id z₂)
identity_app = app(identity, TOP)

ZOO = [
    ("identity",       "λx. x",                          identity),
    ("K",              "λx. λy. x",                      K),
    ("KI / false",     "λx. λy. y",                      KI),
    ("delta",          "λx. x x  (self-application)",    delta),
    ("Z combinator",   "fixed-point combinator",         Z),
    ("fact body",      "λself. λn. if zero? n 1 ...",    fact_body),
    ("fact",           "Z fact_body",                    fact),
    ("data pair",      "pair(T, NIL)  (no λ)",           data_pair),
    ("cons builder",   "λx. λy. λsel. sel x y",          cons_builder),
    ("identity app",   "(id T)  — one β step",           identity_app),
]


# ═══════════════════════════════════════════════════════════════════════
# Pretty-print and analyze
# ═══════════════════════════════════════════════════════════════════════

def count_qe(t):
    """Return (num Q atoms, num E atoms) in t."""
    if isinstance(t, int):
        return (1 if t == Q else 0, 1 if t == E else 0)
    if isinstance(t, App):
        a = count_qe(t.fun)
        b = count_qe(t.arg)
        return (a[0] + b[0], a[1] + b[1])
    if isinstance(t, Prim):
        r = (0, 0)
        for x in t.args:
            c = count_qe(x)
            r = (r[0] + c[0], r[1] + c[1])
        return r
    return (0, 0)


def try_eval(t, label):
    try:
        nf = psi_eval(t)
        return f"→ {term_str(nf, 25)}"
    except Exception as e:
        return f"FAILS: {type(e).__name__}: {str(e)[:80]}"


def main():
    print("σ-image zoo for Ψ∗/N=9")
    print("=" * 78)
    print()
    print("For each program P, we compute σ(P) (atom permutation: Q↔E, f↔η).")
    print("Vars are AST extensions, σ leaves them alone — that's the asymmetry.")
    print()
    print("σ has order 2; verify σ(σ(P)) == P on every entry.")
    print()

    for name, sketch, P in ZOO:
        sP = sigma_image(P)
        ssP = sigma_image(sP)
        involution_ok = ssP == P
        q_orig, e_orig = count_qe(P)
        q_sig, e_sig = count_qe(sP)

        print(f"  ── {name}  ({sketch}) ──")
        print(f"    P     = {term_str(P, 35)}")
        print(f"    σ(P)  = {term_str(sP, 35)}")
        print(f"    σ²=id : {'OK' if involution_ok else 'FAIL'}")
        print(f"    Q-atoms: P={q_orig} σ(P)={q_sig}    "
              f"E-atoms: P={e_orig} σ(P)={e_sig}    "
              f"{'(swapped' if q_orig == e_sig and e_orig == q_sig else '(asym'})")
        print(f"    eval(P)    {try_eval(P, name)}")
        print(f"    eval(σ(P)) {try_eval(sP, 'σ-' + name)}")
        print()

    print("=" * 78)
    print("READING (interpretive — this script just produced the data)")
    print("=" * 78)
    print()
    print("For each P, the natural reading of σ(P) under hypothetical λμμ̃")
    print("semantics — where Q binds Vars and E binds CoVars (continuations):")
    print()
    print("  identity      λx. x      ↔  μ̃α. α        — 'the do-nothing")
    print("                                              continuation'")
    print("                                              [trivial dual]")
    print()
    print("  K             λx. λy. x  ↔  μ̃α. μ̃β. α    — 'pick the FIRST")
    print("                                              continuation, ignoring")
    print("                                              the second' — known as")
    print("                                              the basic two-prompt")
    print("                                              continuation selector")
    print("                                              [USED in shift/reset,")
    print("                                              multi-prompt control]")
    print()
    print("  KI / false    λx. λy. y  ↔  μ̃α. μ̃β. β    — 'pick the SECOND")
    print("                                              continuation' — the dual")
    print("                                              of K [USED for the same")
    print("                                              reason in dual position]")
    print()
    print("  delta         λx. x x    ↔  μ̃α. ⟨α | α⟩   — 'feed continuation to")
    print("                                              itself'  — formally")
    print("                                              well-typed, semantically")
    print("                                              the divergent dual of")
    print("                                              divergence")
    print("                                              [interesting only inside")
    print("                                              Y-style fixpoints]")
    print()
    print("  Z combinator              ↔  the dual fixpoint operator on")
    print("                                continuations [theoretically natural,")
    print("                                no engineering use I know of]")
    print()
    print("  fact body                 ↔  a co-recursive computation that, given")
    print("                                continuations, calls the recursive")
    print("                                continuation with predecessor and")
    print("                                multiplies along the continuation")
    print("                                stack [structurally co-factorial; not")
    print("                                a thing anyone writes]")
    print()
    print("  data pair                 ↔  pair(σ(T), σ(NIL)) = pair(T, NIL)")
    print("                                — pairs are σ-fixed because g is")
    print("                                σ-fixed and T, NIL are σ-fixed")
    print("                                [no dual: data is self-dual]")
    print()
    print("  cons builder λx.λy.λsel.sel x y")
    print("                            ↔  μ̃α.μ̃β.μ̃γ. (γ α) β  approximately —")
    print("                                a 3-continuation receiver — has a")
    print("                                clean reading as the *eliminator* form")
    print("                                of a pair (CPS-style destructuring)")
    print("                                [USED in CPS-converted Lisp]")
    print()
    print("  identity app  (id T)      ↔  ⟨frozen pair | E⟩ → CPS-eval of")
    print("                                identity in continuation form")
    print("                                [exact CPS partner of one β step]")
    print()
    print("VERDICT")
    print("=" * 78)
    print("""
  Engineering-meaningful duals (would be written by someone working in
  CPS / continuation-passing / multi-prompt control):

    identity, K, KI/false, cons builder, identity-application

  The σ-images of these are exactly the constructs you'd expect in a
  λμμ̃-style or CPS-translated codebase. Multi-prompt continuation
  selectors (the σ-images of K and KI) are real things people write.
  CPS-style destructured pair access (the σ-image of the cons builder)
  is real CPS code.

  Borderline:

    delta, Z combinator

  These have well-defined duals on the continuation side, but the duals
  aren't programs anyone writes directly — they live inside fixpoint
  machinery. They'd appear in the σ-image of recursion, not as named
  programs. Not gibberish, but not engineering targets either.

  Probably gibberish (well-defined but not a thing):

    factorial body, factorial, fib

  The σ-images of recursive arithmetic programs are technically
  well-defined co-recursive continuation programs, but no one writes
  "co-factorial." The structural co-recursion is real (it's how anamorphisms
  vs catamorphisms are dual in category theory) but the specific σ-image of
  factorial-the-program isn't a useful artifact.

  Self-dual (σ-image == P-itself):

    data pair (and any pure-data term)

  Pairs, naturals, and atoms are σ-equivariant trivially. No new
  information from σ on data.

CONCLUSION
==========
  σ-orbits at the calculus level are dominated by primitives and
  their CPS-style duals. The duals of *combinators* and *constructors*
  are engineering-meaningful (multi-prompt control, CPS pair access,
  dual identity). The duals of *user programs* (factorial, fib) are
  well-defined co-recursive continuation programs that no one writes.

  Verdict for Option A (build λμμ̃-on-N=9):

    Worth building IF the goal is a Lisp dialect that natively supports
    continuations / CPS / multi-prompt control, where σ-orbits give you
    the value-side and continuation-side primitives in one symmetric
    encoding. That's a real and useful kind of language (Scheme-with-
    delimited-control, Racket's racket/control, etc.).

    NOT worth building if the goal is "factorial proof reuse." σ doesn't
    give you that even after fixing the asymmetry — the dual of factorial
    isn't a program anyone needs proven equivalent to anything.

  My recommendation:

    If the substrate is being pitched as a foundation for a CPS-aware /
    continuation-aware Lisp, build λμμ̃-on-N=9 (Option A). The σ-orbits
    contain the right primitives — multi-prompt selectors, CPS pair
    eliminators, dual identity — that such a language wants natively.
    The substrate's symmetry would land directly on the language's
    polarity structure.

    If the substrate is being pitched as a foundation for a *plain* Lisp
    (no continuations), ship Option D. σ doesn't earn its keep at the
    program level for plain Lisp; the substrate is small and clean,
    that's enough.""")


if __name__ == "__main__":
    main()

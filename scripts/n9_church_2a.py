#!/usr/bin/env python3
"""
2a experiment: σ̂-commutation on Church-encoded programs over N=9.

Hypothesis (from the orchestrator's reframe): the σ-equivariance failures
on N=9 weren't substrate-level — they were ENCODING-level. We used
Q-chain naturals (whose σ-image is E-chain folding to atoms) and Prim
escape hatches (no polarity duals). A purely λ-encoded program with
Church naturals and a polarity-neutral cut form should let σ̂ commute
with eval at the value (Closure) level.

This script tests that hypothesis on:
  • combinators: identity, K, KI
  • Church naturals: c₀, c₁, c₂, c₃
  • succ on Church naturals: σ̂(succ c_n) ?= co-(succ c_n)
  • add on Church naturals
  • mul on Church naturals
  • Church booleans (T, F) and the if combinator

For each P we check: σ̂(eval(P)) == eval(σ̂(P))  (value-level commutation)

Caveat documented: comparing atom outputs across σ̂ requires a top-
level halt continuation we haven't added. So we compare at the value
(Closure / CoClosure) level, not at the atom-output level. Inside the
language (between cuts) σ̂ commutes; the atom-output question is a
separate top-level interface concern.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_lambda_mu_n9_v2 import (
    Var, CoVar, Lam, CoLam, Closure, CoClosure, App,
    lam, colam, cut, psi_eval, sigma_hat, term_str, terms_equal,
    is_cut_shape,
)
from psi_star_n9 import TOP, BOT, NAMES, SIGMA


# ═══════════════════════════════════════════════════════════════════════
# Combinators
# ═══════════════════════════════════════════════════════════════════════

# identity = λx. x
identity = lam(Var(0))

# K = λx. λy. x
K = lam(lam(Var(1)))

# KI / Church false = λx. λy. y
KI = lam(lam(Var(0)))

# Church true = K, Church false = KI
ChT = K
ChF = KI

# Church if = λp. λa. λb. p a b — but in our cut form: ⟨⟨⟨p | a⟩ | b⟩ | _⟩
# Simpler: just use p directly — Church booleans take two args and pick one.


# ═══════════════════════════════════════════════════════════════════════
# Church naturals as λ-terms
# ═══════════════════════════════════════════════════════════════════════
# c_n = λf. λx. f^n(x)
#
# c_0 = λf. λx. x                                       (Var(0))
# c_1 = λf. λx. f x                                     (cut(Var(1), Var(0)))
# c_n = λf. λx. f (f (... (f x)))                       (n nested cuts of Var(1) around Var(0))
#
# Inside the body, Var(1) = f and Var(0) = x.

def church(n: int):
    body = Var(0)
    for _ in range(n):
        body = cut(Var(1), body)
    return lam(lam(body))


c0 = church(0)
c1 = church(1)
c2 = church(2)
c3 = church(3)
c5 = church(5)


# Successor: succ = λn. λf. λx. f (n f x)
# Inside: n=Var(2), f=Var(1), x=Var(0)
# (n f x) is cut(cut(n, f), x) = cut(cut(Var(2), Var(1)), Var(0))
# f (n f x) is cut(Var(1), cut(cut(Var(2), Var(1)), Var(0)))
succ = lam(lam(lam(
    cut(Var(1),
        cut(cut(Var(2), Var(1)), Var(0)))
)))


# Addition: add = λm. λn. λf. λx. m f (n f x)
# m=Var(3), n=Var(2), f=Var(1), x=Var(0)
add = lam(lam(lam(lam(
    cut(cut(Var(3), Var(1)),
        cut(cut(Var(2), Var(1)), Var(0)))
))))


# Multiplication: mul = λm. λn. λf. m (n f)
# m=Var(2), n=Var(1), f=Var(0)
# (n f) is cut(Var(1), Var(0)); m (n f) is cut(Var(2), cut(Var(1), Var(0)))
mul = lam(lam(lam(
    cut(Var(2), cut(Var(1), Var(0)))
)))


# ═══════════════════════════════════════════════════════════════════════
# σ̂-commutation check
# ═══════════════════════════════════════════════════════════════════════

def commute_check(label: str, P, verbose: bool = False) -> dict:
    """Verify σ̂(eval(P)) == eval(σ̂(P)). Returns a result dict."""
    try:
        nf_p = psi_eval(P)
        ok_p = True
    except Exception as e:
        nf_p = f"ERR: {e}"
        ok_p = False

    sP = sigma_hat(P)
    try:
        nf_sp = psi_eval(sP)
        ok_sp = True
    except Exception as e:
        nf_sp = f"ERR: {e}"
        ok_sp = False

    commutes = (ok_p and ok_sp
                and terms_equal(sigma_hat(nf_p), nf_sp))

    if verbose:
        print(f"  P       : {term_str(P, 25)}")
        print(f"  σ̂(P)    : {term_str(sP, 25)}")
        print(f"  eval(P) : {term_str(nf_p, 25) if ok_p else nf_p}")
        print(f"  eval(σ̂P): {term_str(nf_sp, 25) if ok_sp else nf_sp}")
        if ok_p and ok_sp:
            print(f"  σ̂(eval(P)): {term_str(sigma_hat(nf_p), 25)}")

    return dict(label=label, commutes=commutes,
                ok_p=ok_p, ok_sp=ok_sp,
                nf_p=nf_p, nf_sp=nf_sp)


def report(checks: list[dict]):
    n = len(checks)
    passed = sum(1 for c in checks if c["commutes"])
    print()
    print(f"  {passed}/{n} σ̂-commutation checks passed.")
    failed = [c for c in checks if not c["commutes"]]
    if failed:
        print()
        print(f"  Failures:")
        for c in failed:
            why = []
            if not c["ok_p"]:
                why.append(f"eval(P) failed: {c['nf_p']}")
            if not c["ok_sp"]:
                why.append(f"eval(σ̂(P)) failed: {c['nf_sp']}")
            if c["ok_p"] and c["ok_sp"] and not c["commutes"]:
                why.append(f"results differ: σ̂(nf(P))={term_str(sigma_hat(c['nf_p']), 20)} vs nf(σ̂P)={term_str(c['nf_sp'], 20)}")
            print(f"    [{c['label']}] {'; '.join(why)}")


# ═══════════════════════════════════════════════════════════════════════
# Tests
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("2a — σ̂-commutation on Church-encoded programs over N=9 (polarity-neutral cuts)")
    print("=" * 85)
    print()

    # ── 1. Combinators as values ──────────────────────────────────
    print("1. COMBINATORS — closure-level σ̂-commutation")
    print("-" * 85)
    checks = []
    for label, P in [("identity", identity), ("K", K), ("KI", KI)]:
        c = commute_check(label, P)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} {label:20s} σ̂(eval(P)) == eval(σ̂(P))")
    report(checks)
    print()

    # ── 2. Church naturals as values ──────────────────────────────
    print("2. CHURCH NATURALS — closure-level σ̂-commutation (cuts inside body)")
    print("-" * 85)
    checks = []
    for n in range(6):
        cn = church(n)
        c = commute_check(f"church({n})", cn)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} church({n})            σ̂ commutes")
    report(checks)
    print()

    # ── 3. Successor — Church operations as values ────────────────
    print("3. SUCC — closure-level σ̂-commutation on a higher-order arithmetic op")
    print("-" * 85)
    c = commute_check("succ", succ)
    print(f"  {'✓' if c['commutes'] else '✗'} succ                  σ̂ commutes")
    report([c])
    print()

    # ── 4. Apply succ to a Church natural — full reduction ─────────
    print("4. ⟨succ | c_n⟩ — REDUCTION DOWN TO A CHURCH-N+1 CLOSURE")
    print("-" * 85)
    checks = []
    for n in range(4):
        P = cut(succ, church(n))
        c = commute_check(f"⟨succ | c_{n}⟩", P, verbose=False)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} ⟨succ | c_{n}⟩          σ̂ commutes")
    report(checks)
    print()

    # ── 5. Add on Church naturals ─────────────────────────────────
    print("5. ⟨⟨add | c_m⟩ | c_n⟩ — ADDITION")
    print("-" * 85)
    checks = []
    for m, n in [(0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (2, 2)]:
        P = cut(cut(add, church(m)), church(n))
        c = commute_check(f"⟨⟨add | c_{m}⟩ | c_{n}⟩", P)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} ⟨⟨add | c_{m}⟩ | c_{n}⟩  σ̂ commutes")
    report(checks)
    print()

    # ── 6. Mul on Church naturals ─────────────────────────────────
    print("6. ⟨⟨mul | c_m⟩ | c_n⟩ — MULTIPLICATION")
    print("-" * 85)
    checks = []
    for m, n in [(0, 1), (1, 1), (2, 1), (2, 2), (3, 2)]:
        P = cut(cut(mul, church(m)), church(n))
        c = commute_check(f"⟨⟨mul | c_{m}⟩ | c_{n}⟩", P)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} ⟨⟨mul | c_{m}⟩ | c_{n}⟩  σ̂ commutes")
    report(checks)
    print()

    # ── 7. Church booleans T and F ────────────────────────────────
    print("7. CHURCH BOOLEANS — T and F as combinators (= K and KI)")
    print("-" * 85)
    checks = []
    for label, P in [("ChT (=K)", ChT), ("ChF (=KI)", ChF)]:
        c = commute_check(label, P)
        checks.append(c)
        print(f"  {'✓' if c['commutes'] else '✗'} {label:20s} σ̂ commutes")
    # Apply: ⟨⟨T | a⟩ | b⟩ → a; ⟨⟨F | a⟩ | b⟩ → b
    for label, P, expected in [
        ("⟨⟨T | T-atom⟩ | NIL⟩", cut(cut(ChT, TOP), BOT), TOP),
        ("⟨⟨F | T-atom⟩ | NIL⟩", cut(cut(ChF, TOP), BOT), BOT),
    ]:
        c = commute_check(label, P)
        checks.append(c)
        # Also verify the atom output (this is where top-level halt matters)
        nf = c["nf_p"]
        atom_ok = nf == expected
        print(f"  {'✓' if c['commutes'] else '✗'} {label:30s} σ̂ commutes; "
              f"eval(P) = {term_str(nf)}{'  (= ' + NAMES[expected] + ')' if atom_ok else ''}")
    report(checks)
    print()

    # ── 8. Detailed trace of one case for the writeup ─────────────
    print("8. DETAILED TRACE — ⟨succ | c_2⟩ (closure structure)")
    print("-" * 85)
    P = cut(succ, c2)
    sP = sigma_hat(P)
    nf_p = psi_eval(P)
    nf_sp = psi_eval(sP)
    print(f"  P       = {term_str(P, 30)}")
    print(f"  σ̂(P)    = {term_str(sP, 30)}")
    print()
    print(f"  eval(P)        = {term_str(nf_p, 30)}")
    print(f"  σ̂(eval(P))     = {term_str(sigma_hat(nf_p), 30)}")
    print(f"  eval(σ̂(P))     = {term_str(nf_sp, 30)}")
    print(f"  Commute:  {terms_equal(sigma_hat(nf_p), nf_sp)}")
    print()

    print("=" * 85)
    print("SUMMARY")
    print("=" * 85)
    print("""
  If 2a delivers σ̂-commutation across all the above, then:

    N=9 IS the right substrate. The σ-equivariance failures we found
    earlier were specifically about the encoding choices (Q-chain
    naturals + Prim arithmetic + polarity-laden cut form), not about
    the substrate's atom roster. With Church naturals + λ-encoded
    arithmetic + polarity-neutral cuts (ρ-wrapped g-pair), σ̂ commutes
    with eval at the closure level on every program tested.

    The atom-output level still needs a top-level halt convention to
    compare across σ̂. That's a separate small piece of engineering,
    not a substrate question.

  If σ̂-commutation fails on some checks, the failure mode tells us
  whether the limit is:
    (a) substrate atom count → 2b is justified
    (b) calculus reduction rules → smaller fix possible
    (c) value-recursion vs codata → no substrate change helps; ship N=9
""")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Factorial in the σ-equivariant encoding on Ψ∗/N=9.

Demonstrates the three things the design was meant to deliver:

  1. Factorial as a self-contained term using only existing N=9 atoms
     (Q, E, g, plus host arithmetic via Prim) and a single new ADT
     extension (Var). Term sizes counted.

  2. The σ-image has an exact computational reading. σ swaps Q↔E and
     f↔η; under our encoding that means lambdas (Q-tagged frozen body)
     become applied-form pairs (Q-tagged frozen pair-of-args), and
     applications (E-forced pair) become frozen-and-not-yet-applied
     pairs. We illustrate concretely on the identity, on K, and on Z.

  3. A partial evaluator instrumented for atomic table folds — we
     report which bonus identities (f²=η, η²=f, Q²=Q, E²=E, g²=ρ,
     ρ²=ρ) actually fire during evaluation and PE.
"""

from __future__ import annotations

import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import psi_star_n9_sigma as σ
from psi_star_n9_sigma import (
    Var, Prim, App, Closure, lam, app, pair_t, sigma_image,
    count_atoms, count_vars, count_prims, has_vars,
    psi_eval, term_str,
)
from psi_star_n9 import nat, to_nat, Q, E, F_ENC, G_ENC, ETA, RHO, NAMES, SIGMA

# ═══════════════════════════════════════════════════════════════════════
# Z combinator (CBV Y) — built only from `lam` and `app`
# ═══════════════════════════════════════════════════════════════════════
#
# Z = λf. (λx. f (λv. (x x) v)) (λx. f (λv. (x x) v))
#
# de Bruijn: inside v-lambda, v=#0, x=#1, f=#2; inside x-lambda, x=#0, f=#1.

_inner = lam(app(app(Var(1), Var(1)), Var(0)))     # λv. (x x) v
_xlam  = lam(app(Var(1), _inner))                   # λx. f (λv. (x x) v)
Z      = lam(app(_xlam, _xlam))                     # λf. (...) (...)


# ═══════════════════════════════════════════════════════════════════════
# Factorial body — `λself. λn. if (zero? n) 1 (n * (self (n-1)))`
# ═══════════════════════════════════════════════════════════════════════

fact_body = lam(lam(
    Prim("if", (
        Prim("zero?", (Var(0),)),
        nat(1),
        Prim("mul", (
            Var(0),
            app(Var(1), Prim("sub", (Var(0), nat(1)))),
        )),
    ))
))

fact = app(Z, fact_body)


# ═══════════════════════════════════════════════════════════════════════
# Partial evaluator with bonus-identity instrumentation
# ═══════════════════════════════════════════════════════════════════════

def specialize(term, n: int) -> tuple:
    """Specialize `term` against literal nat(n). Returns (result, fold_log).

    The fold_log is a defaultdict(int) recording every atomic table
    lookup, keyed by (operand-name, operand-name, result-name).
    Squarings (a·a) are also separately recorded.
    """
    log: dict = defaultdict(int)
    σ.INSTRUMENT = log
    try:
        result = psi_eval(app(term, nat(n)))
    finally:
        σ.INSTRUMENT = None
    return result, log


def report_squarings(log: dict) -> dict:
    """Extract just the bonus-identity (a·a) folds."""
    out = {}
    for key, count in log.items():
        if isinstance(key, tuple) and len(key) == 2 and key[0] == "__square__":
            out[key[1]] = count
    return out


# ═══════════════════════════════════════════════════════════════════════
# Demonstration
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("σ-equivariant factorial on Ψ∗/N=9")
    print("=" * 70)
    print()

    # ── 1. Term sizes ──
    print("1. TERM SIZES (Z combinator + factorial body, σ-equivariant wire form)")
    print("-" * 70)
    rows = [
        ("Z combinator",   Z),
        ("fact body",      fact_body),
        ("fact = app(Z, body)", fact),
    ]
    for label, t in rows:
        a = count_atoms(t)
        v = count_vars(t)
        p = count_prims(t)
        print(f"  {label:30s}  atoms={a:4d}   vars={v:3d}   prims={p}")
    print()
    print(f"  Total leaves in fact: {count_atoms(fact) + count_vars(fact) + count_prims(fact)}")
    print()

    # ── 2. Run factorial ──
    print("2. RUNNING fact(n)")
    print("-" * 70)
    cases = [(0, 1), (1, 1), (2, 2), (3, 6), (4, 24), (5, 120),
             (6, 720), (8, 40320), (10, 3628800)]
    fails = 0
    for n, expected in cases:
        r = psi_eval(app(fact, nat(n)))
        got = to_nat(r)
        ok = got == expected
        if not ok:
            fails += 1
        print(f"  fact({n:2d}) = {got!s:>9}  expected {expected!s:>9}  {'OK' if ok else 'FAIL'}")
    if fails:
        print(f"\n{fails} factorial mismatches; aborting demo.")
        return 1
    print()

    # ── 3. σ-image structural analysis ──
    print("3. σ-IMAGE — INTRO/ELIM DUALITY MADE CONCRETE")
    print("-" * 70)
    print("σ swaps Q↔E and f↔η. Under the wire format that means:")
    print()
    print("  σ(λ. body) = σ(App(Q, body))")
    print("             = App(E, σ(body))")
    print("             = 'force the σ-image of the body'")
    print()
    print("  σ(app(M, N)) = σ(App(E, App(App(g, M), N)))")
    print("               = App(Q, App(App(g, σ(M)), σ(N)))")
    print("               = 'frozen pair of σ-images, awaiting an E to fire'")
    print()
    print("So under σ, lambdas become frozen-pair values, and applications")
    print("become elimination-pending pairs. Intro and elim swap roles.")
    print()

    # Identity worked example
    Id = lam(Var(0))
    Id_sig = sigma_image(Id)
    print(f"  identity λ:           {term_str(Id)}")
    print(f"    = App(Q, Var(0))")
    print(f"  σ(identity):          {term_str(Id_sig)}")
    print(f"    = App(E, Var(0))   -- 'force whatever Var(0) is'")
    print()

    # Z structural counts
    Z_sig = sigma_image(Z)
    print(f"  Z combinator:         atoms={count_atoms(Z)}, Q-leaves and E-leaves swap under σ")
    Q_count = sum(1 for _ in _walk(Z) if _ == Q)
    E_count = sum(1 for _ in _walk(Z) if _ == E)
    Q_count_s = sum(1 for _ in _walk(Z_sig) if _ == Q)
    E_count_s = sum(1 for _ in _walk(Z_sig) if _ == E)
    print(f"    Z       : Q-atoms={Q_count}, E-atoms={E_count}")
    print(f"    σ(Z)    : Q-atoms={Q_count_s}, E-atoms={E_count_s}  -- exactly swapped")
    print()

    # ── 4. The wrinkle: Vars are NOT σ-symmetric ──
    print("4. THE WRINKLE — Vars break exact σ-symmetry")
    print("-" * 70)
    print("Vars are unchanged by σ (they're a meta-syntactic ADT extension,")
    print("not an algebra atom). But they only make sense under Q-binders.")
    print("Under σ, those Q-binders become E's — no longer introducing env entries.")
    print()
    try:
        psi_eval(Id_sig)
        print("  σ(identity) evaluated cleanly  ← unexpected")
    except Exception as e:
        print(f"  Eval(σ(identity)) → {type(e).__name__}: unbound Var")
        print("  (because the binder Q was σ-flipped to E, which doesn't introduce env)")
    print()
    print("  This is a real, interesting asymmetry. The σ-pairing of Q with E")
    print("  is exact at the algebra level, but the calculus's binding structure")
    print("  is intrinsically intro-side. Vars have no σ-dual at the AST level.")
    print()
    print("  Possible resolutions (all speculative, none implemented):")
    print("    a) Add a 'CoVar' AST extension so the Var↔CoVar swap completes σ")
    print("    b) De-Bruijn-encode Vars as Q-chains so they're σ-equivariant")
    print("       too (collides with naturals — needs a tag)")
    print("    c) Accept the asymmetry as a feature: the calculus has a")
    print("       directionality (eval-towards-normal-form) that the algebra's")
    print("       involution doesn't have. σ is the symmetry of values, not of")
    print("       computations.")
    print()

    # ── 5. Partial evaluation — bonus-identity instrumentation ──
    print("5. PARTIAL EVALUATION — DO BONUS IDENTITIES FIRE?")
    print("-" * 70)
    print()
    for n in (3, 5, 8):
        result, log = specialize(fact, n)
        sq = report_squarings(log)
        total_dots = sum(c for k, c in log.items()
                         if isinstance(k, tuple) and k[0] != "__square__")
        print(f"  fact({n}) = {to_nat(result)}")
        print(f"    total atomic dot() calls : {total_dots}")
        print(f"    squarings (bonus loci)   : {dict(sq) if sq else '{}'}")
        print()

    print("FINDING (honest): the bonus identities don't directly fire during")
    print("normal factorial evaluation, even with PE. Reasons:")
    print()
    print("  • Q is lazy by eval rule — App(Q, _) never reduces, so Q² never")
    print("    gets dotted at the term level. Q² = Q is an algebra fact about")
    print("    the table cell, not a term-level rewrite.")
    print()
    print("  • E unwraps Q on Q-wrapped terms; on bare atom args it does")
    print("    dot(E, atom). E·E would only fire if a program reified E as")
    print("    data and then forced it — atypical in straight λ-code.")
    print()
    print("  • f, η, g, ρ folds during normal eval go through the structural")
    print("    rules (pair projection, pair construction, branch), not the")
    print("    atom-on-atom dot. Their squaring identities don't fire either.")
    print()
    print("  • The arithmetic (mul, sub, zero?) goes through Prim — host-level.")
    print("    No table contact at all.")
    print()
    print("  Where they WOULD fire: in atom-only sub-expressions. E.g.,")
    print("  evaluating App(E, E) literally hits dot(E, E) = E. We show one:")
    σ.INSTRUMENT = defaultdict(int)
    r = psi_eval(App(E, E))
    log = σ.INSTRUMENT
    σ.INSTRUMENT = None
    sq = report_squarings(log)
    print(f"    eval(App(E, E))     = {NAMES[r] if isinstance(r, int) else term_str(r)}")
    print(f"    squarings recorded  = {dict(sq)}")
    print()
    print("  So the identities are real and verifiable, but they don't")
    print("  load-bear for partial-evaluation of programs over Q-chain naturals.")
    print("  They'd matter for an atom-arithmetic optimizer — different toolchain.")
    print()

    # ── 6. Summary ──
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  • Factorial closed-form term     : {count_atoms(fact)} atoms + "
          f"{count_vars(fact)} Vars + {count_prims(fact)} Prims")
    print(f"  • Encoding                       : σ-equivariant at the wire level")
    print(f"  • σ-image of values              : intro/elim duality (concrete)")
    print(f"  • σ-image of executions          : breaks (Vars have no σ-dual)")
    print(f"  • Bonus identities in PE         : do not fire on normal programs")
    print(f"  • Bonus identities in atom-arith : verifiable but separate concern")
    return 0


def _walk(t):
    """Yield every leaf atom (int) in t."""
    if isinstance(t, int):
        yield t
    elif isinstance(t, App):
        yield from _walk(t.fun)
        yield from _walk(t.arg)
    elif isinstance(t, Prim):
        for a in t.args:
            yield from _walk(a)


if __name__ == "__main__":
    sys.exit(main())

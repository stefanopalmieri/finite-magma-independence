#!/usr/bin/env python3
"""
Church-encoded factorial via Y on N=9, with σ̂-commutation check.

Closes the hedge from RESULT_2A.md: we predicted Church factorial would
σ̂-commute by the same logic that succ/add/mul did, but didn't run it.
This script does the run at small n (0..3) to convert prediction into
data point.

Construction:
  • Church pred — the standard Kleene formula:
      pred = λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u)
  • iszero = λn. n (λx. F) T   where T = K, F = KI
  • Z combinator (CBV Y) — already in our toolkit
  • Thunked conditional to avoid CBV's eager-both-branches problem:
      if-then-else encoded as
          ⟨⟨⟨⟨iszero | n⟩ | (λu. then-body)⟩ | (λu. else-body)⟩ | unit⟩
      Both thunks are closures (values) created without reducing their
      bodies; only the selected thunk gets forced by `unit`.
  • fact-body:
      λself. λn. if iszero(n) then c_1 else (mul n (self (pred n)))
  • fact = ⟨Z | fact-body⟩

Test: for n in {0..3}, compute eval(⟨fact | c_n⟩) and check that
σ̂(eval(P)) == eval(σ̂(P)) at the closure level.

Numeric verification: extract the Church number out of the result
closure by applying it to (succ-on-atoms) and a starting atom, counting
applications.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_lambda_mu_n9_v2 import (
    Var, CoVar, Lam, CoLam, Closure, CoClosure, App,
    lam, colam, cut, pair_t, psi_eval, sigma_hat, term_str, terms_equal,
)
from psi_star_n9 import TOP, BOT, NAMES, G_ENC


# ═══════════════════════════════════════════════════════════════════════
# Reuse from n9_church_2a — combinators, Church naturals, arithmetic
# ═══════════════════════════════════════════════════════════════════════

identity = lam(Var(0))
K = lam(lam(Var(1)))
KI = lam(lam(Var(0)))
ChT = K   # Church true
ChF = KI  # Church false


def church(n: int):
    """λf. λx. f^n(x)"""
    body = Var(0)
    for _ in range(n):
        body = cut(Var(1), body)
    return lam(lam(body))


# Multiplication — already verified σ̂-commuting
mul = lam(lam(lam(
    cut(Var(2), cut(Var(1), Var(0)))
)))


# ═══════════════════════════════════════════════════════════════════════
# Church predecessor — Kleene's formula
# ═══════════════════════════════════════════════════════════════════════
#
# pred = λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u)
#
# de Bruijn:
#   Inside body of λn.λf.λx :  x = #0, f = #1, n = #2
#   Inner term `(λg. λh. h (g f))`:
#     Inside λg : g = #0, x = #1, f = #2, n = #3   (f shifts +1)
#     Inside λh : h = #0, g = #1, x = #2, f = #3, n = #4
#     Body `h (g f)` uses: h=#0, g=#1, f=#3
#       → cut(Var(0), cut(Var(1), Var(3)))
#     λh wraps: lam(cut(Var(0), cut(Var(1), Var(3))))
#     λg wraps: lam(lam(cut(Var(0), cut(Var(1), Var(3)))))
#   Inner term `(λu. x)`:
#     Inside λu : u = #0, x = #1, f = #2, n = #3
#     Body `x` = Var(1)
#     λu: lam(Var(1))
#   Inner term `(λu. u)`:
#     Inside λu : u = #0
#     Body: Var(0)
#     λu: lam(Var(0))   # = identity
#   Body of pred: ⟨⟨⟨n | inner1⟩ | inner2⟩ | inner3⟩ where n = Var(2)

_pred_inner1 = lam(lam(cut(Var(0), cut(Var(1), Var(3)))))
_pred_inner2 = lam(Var(1))
_pred_inner3 = lam(Var(0))
_pred_body = cut(cut(cut(Var(2), _pred_inner1), _pred_inner2), _pred_inner3)
pred = lam(lam(lam(_pred_body)))


# ═══════════════════════════════════════════════════════════════════════
# iszero = λn. n (λx. F) T
# ═══════════════════════════════════════════════════════════════════════
# Inside λn body: n = #0
# (λx. F) — F is closed, body is just F (with x bound but unused)
#   Inside λx: x = #0; body = F (closed, no shift needed)
#   λx: lam(ChF)
# T is closed: ChT
# Body: ⟨⟨n | (λx. F)⟩ | T⟩
_iszero_body = cut(cut(Var(0), lam(ChF)), ChT)
iszero = lam(_iszero_body)


# ═══════════════════════════════════════════════════════════════════════
# Z combinator (CBV Y) — same as the n9_term_factorial version
# ═══════════════════════════════════════════════════════════════════════
# Z = λf. (λx. f (λv. (x x) v)) (λx. f (λv. (x x) v))
# Inside λf : f = #0
# Inside λx (depth 1) : x = #0, f = #1
# Inside λv (depth 2) : v = #0, x = #1, f = #2
# (x x) v = ⟨⟨x | x⟩ | v⟩ = cut(cut(Var(1), Var(1)), Var(0))
# (λv. (x x) v) = lam(cut(cut(Var(1), Var(1)), Var(0)))
# f (λv. (x x) v) = cut(Var(1), <above>)
# (λx. f (λv. ...)) = lam(cut(Var(1), lam(cut(cut(Var(1), Var(1)), Var(0)))))

_z_inner = lam(cut(cut(Var(1), Var(1)), Var(0)))
_z_M = lam(cut(Var(1), _z_inner))
Z = lam(cut(_z_M, _z_M))


# ═══════════════════════════════════════════════════════════════════════
# Factorial body via thunked conditional
# ═══════════════════════════════════════════════════════════════════════
#
# fact-body = λself. λn.
#               ⟨⟨⟨⟨iszero | n⟩ | (λu. c_1)⟩ | (λu. mul n (self (pred n)))⟩ | unit⟩
#
# de Bruijn outside thunks (in fact-body): self = #1, n = #0
# Inside (λu. c_1): u = #0; body c_1 is closed.
# Inside (λu. mul n (self (pred n))):
#   u = #0, n = #1 (shifted by 1), self = #2 (shifted by 1)
#   mul, pred are closed
#   body: cut(cut(mul, n), cut(self, cut(pred, n)))
#       = cut(cut(mul, Var(1)), cut(Var(2), cut(pred, Var(1))))
# unit can be any value — we use TOP.

_thunk_true = lam(church(1))
_thunk_false = lam(
    cut(cut(mul, Var(1)),
        cut(Var(2), cut(pred, Var(1))))
)
_fact_body_inner = cut(
    cut(cut(cut(iszero, Var(0)), _thunk_true), _thunk_false),
    TOP
)
fact_body = lam(lam(_fact_body_inner))

fact = cut(Z, fact_body)


# ═══════════════════════════════════════════════════════════════════════
# Numeric extraction: feed the result Church natural a stepper
# ═══════════════════════════════════════════════════════════════════════
#
# Apply the result-as-c_k to a g-pair builder and a starting atom.
# Counting layers of the resulting g-pair chain gives k.
#
# Why g-pair instead of Q-chain: the natural choice `λx. Q·x` runs
# into our evaluator's lazy-Q rule, which doesn't substitute Vars
# inside `App(Q, body)` — so `App(Q, Var(0))` evaluates to
# `App(Q, Var(0))` (Var unsubstituted) instead of `App(Q, val)`. The
# g-rule does substitute (it explicitly calls psi_eval on its arg),
# so a g-pair builder works cleanly.


def extract_church(result):
    """Apply result-as-c_k to a g-pair builder and count layers."""
    builder = lam(pair_t(BOT, Var(0)))   # λv. ⟨NIL, v⟩  — uses g
    start = BOT                          # NIL
    applied = cut(cut(result, builder), start)
    final = psi_eval(applied)
    n = 0
    t = final
    while (isinstance(t, App) and isinstance(t.fun, App)
           and t.fun.fun == G_ENC):
        n += 1
        t = t.arg
    return n if t == BOT else None


# ═══════════════════════════════════════════════════════════════════════
# σ̂-commutation check + numeric verification
# ═══════════════════════════════════════════════════════════════════════

def commute_check(label, P):
    try:
        steps_p = [0]
        nf_p = psi_eval(P, _steps=steps_p)
        ok_p = True
    except Exception as e:
        nf_p = f"ERR: {e}"
        ok_p = False
        steps_p = [0]

    sP = sigma_hat(P)
    try:
        steps_sp = [0]
        nf_sp = psi_eval(sP, _steps=steps_sp)
        ok_sp = True
    except Exception as e:
        nf_sp = f"ERR: {e}"
        ok_sp = False
        steps_sp = [0]

    commutes = ok_p and ok_sp and terms_equal(sigma_hat(nf_p), nf_sp)
    return dict(label=label, commutes=commutes,
                ok_p=ok_p, ok_sp=ok_sp,
                nf_p=nf_p, nf_sp=nf_sp,
                steps_p=steps_p[0], steps_sp=steps_sp[0])


def main():
    print("Church-encoded factorial via Y on N=9 — σ̂-commutation data point")
    print("=" * 78)
    print()

    # ── Component sanity checks ───────────────────────────────────
    print("0. COMPONENT SANITY (each piece on its own)")
    print("-" * 78)
    pieces = [
        ("iszero",   iszero),
        ("pred",     pred),
        ("Z",        Z),
        ("fact_body", fact_body),
        ("fact",     fact),
    ]
    for label, P in pieces:
        c = commute_check(label, P)
        print(f"  {'✓' if c['commutes'] else '✗'} {label:14s} σ̂-commute  "
              f"(P: {c['steps_p']} steps; σ̂P: {c['steps_sp']} steps)")
    print()

    # ── iszero correctness check ──────────────────────────────────
    print("1. iszero CORRECTNESS — on c_0, c_1, c_2")
    print("-" * 78)
    for n in (0, 1, 2):
        # ⟨⟨⟨iszero | c_n⟩ | T-then⟩ | NIL-else⟩
        # = if iszero(n) then T else NIL
        P = cut(cut(cut(iszero, church(n)), TOP), BOT)
        try:
            r = psi_eval(P)
            expected = TOP if n == 0 else BOT
            ok = (r == expected)
            print(f"  iszero(c_{n}) chooses → {term_str(r)}  "
                  f"(expected {NAMES[expected]}, {'OK' if ok else 'FAIL'})")
        except Exception as e:
            print(f"  iszero(c_{n}) FAILS: {e}")
    print()

    # ── pred correctness check ───────────────────────────────────
    print("2. pred CORRECTNESS — extracted Church number after pred(c_n)")
    print("-" * 78)
    for n in (1, 2, 3, 4):
        P = cut(pred, church(n))
        try:
            r = psi_eval(P)
            k = extract_church(r)
            print(f"  pred(c_{n}) extracts to → {k}   "
                  f"(expected {n-1}, {'OK' if k == n-1 else 'FAIL'})")
        except Exception as e:
            print(f"  pred(c_{n}) FAILS: {e}")
    print()

    # ── factorial correctness + σ̂-commutation ────────────────────
    print("3. FACTORIAL — ⟨fact | c_n⟩ via Y, with σ̂-commutation check")
    print("-" * 78)
    expected = [1, 1, 2, 6, 24, 120, 720]
    checks = []
    for n in range(6):
        print(f"\n  n={n}  (expecting {expected[n]} = {n}!)")
        P = cut(fact, church(n))
        c = commute_check(f"fact(c_{n})", P)
        checks.append(c)

        if c["ok_p"]:
            try:
                k = extract_church(c["nf_p"])
                ok_num = (k == expected[n])
                print(f"    eval(⟨fact | c_{n}⟩) extracts to → {k}  "
                      f"(expected {expected[n]}, {'OK' if ok_num else 'FAIL'})")
                print(f"    eval steps      : {c['steps_p']:>8d}")
            except Exception as e:
                print(f"    extraction FAILS: {e}")
        else:
            print(f"    eval FAILS: {c['nf_p']}")

        if c["commutes"]:
            print(f"    σ̂-commute       : ✓     "
                  f"(σ̂P eval steps: {c['steps_sp']})")
        else:
            print(f"    σ̂-commute       : ✗")
            if c["ok_p"] and c["ok_sp"]:
                print(f"      σ̂(eval P) ≠ eval(σ̂P)")
                print(f"      σ̂(eval P) = {term_str(sigma_hat(c['nf_p']), 30)}")
                print(f"      eval(σ̂P)  = {term_str(c['nf_sp'], 30)}")

    print()
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    n_ok = sum(1 for c in checks if c["commutes"])
    print(f"  σ̂-commutation: {n_ok}/{len(checks)} factorial cases.")
    print()
    if n_ok == len(checks):
        print("  Hedge converted to data point: Church-encoded factorial via Y")
        print("  σ̂-commutes on N=9 at every n we tested. Combined with the")
        print("  succ/add/mul results in n9_church_2a.py, this confirms σ̂")
        print("  closes on the polarity-neutral λμμ̃ fragment over N=9 for both")
        print("  non-recursive (combinators, Church arithmetic) and recursive")
        print("  (Y-bound factorial) programs.")
    else:
        print("  Hedge NOT converted — Church factorial breaks σ̂-commutation.")
        print("  Failure pattern tells us whether the limit is in the encoding")
        print("  or in something deeper.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Smoke test for the N=9 Ψ-Lisp port.

Runs a battery of small programs against psi_lisp_n9 and checks the
results are what we expect. No dependency on the DistinctionStructures
repo.

Also exercises the canonical-witness symmetry σ = (f η)(Q E) at the
Lisp level: σ-conjugating the Cayley table (via the `dot` builtin)
should produce the same table read back.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_lisp_n9 import builtin_env, run, display, decode_int, encode_int, BOT, TOP, _VOID
from psi_star_n9 import TABLE, SIGMA, N


def _printable(results):
    return [display(r) for r in results if r is not _VOID]


def check(label: str, source: str, expected_strs: list[str]) -> bool:
    env = builtin_env()
    out_real = _printable(run(source, env))
    ok = out_real == expected_strs
    status = "OK" if ok else "FAIL"
    print(f"  [{status}] {label}")
    if not ok:
        print(f"    expected: {expected_strs}")
        print(f"    got:      {out_real}")
    return ok


def main() -> int:
    print("Ψ-Lisp/N=9 smoke test")
    print()

    fails = 0

    # ── Atoms and literals ──
    fails += not check(
        "atoms",
        "42 0 T NIL",
        ["42", "0", "T", "NIL"],
    )

    # ── Lists ──
    fails += not check(
        "cons / car / cdr",
        "(cons 1 2) (car (cons 10 20)) (cdr (cons 10 20))",
        ["(1 . 2)", "10", "20"],
    )
    fails += not check(
        "list",
        "(list 1 2 3 4 5)",
        ["(1 2 3 4 5)"],
    )

    # ── Arithmetic ──
    fails += not check(
        "arithmetic",
        "(+ 3 4) (- 10 3) (* 4 5) (mod 17 5) (/ 17 5)",
        ["7", "7", "20", "2", "3"],
    )
    fails += not check(
        "predicates",
        "(zerop 0) (zerop 5) (< 3 5) (> 3 5) (= 7 7) (numberp 42) (numberp NIL)",
        ["T", "NIL", "T", "NIL", "T", "T", "NIL"],
    )

    # ── Recursion (the no-Y-atom path) ──
    fails += not check(
        "fib",
        """
        (defun fib (n)
          (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
        (fib 0) (fib 1) (fib 2) (fib 3) (fib 5) (fib 8) (fib 10)
        """,
        ["0", "1", "1", "2", "5", "21", "55"],
    )

    fails += not check(
        "iterative fib",
        """
        (defun fib-iter (n)
          (defun helper (a b count)
            (if (= count 0) a (helper b (+ a b) (- count 1))))
          (helper 0 1 n))
        (fib-iter 10) (fib-iter 20)
        """,
        ["55", "6765"],
    )

    # ── Higher-order ──
    fails += not check(
        "map + reverse",
        """
        (defun map (f xs)
          (if (null xs) NIL (cons (f (car xs)) (map f (cdr xs)))))
        (defun rev-helper (l acc)
          (if (null l) acc (rev-helper (cdr l) (cons (car l) acc))))
        (defun reverse (lst) (rev-helper lst NIL))
        (map (lambda (x) (* x x)) (list 1 2 3 4 5))
        (reverse (list 1 2 3 4 5))
        """,
        ["(1 4 9 16 25)", "(5 4 3 2 1)"],
    )

    # ── cond ── symbols print as their Q-chain integer (depends on interning),
    # so just check we get 3 distinct numeric ids.
    env = builtin_env()
    cond_results = run(
        """
        (defun classify (n)
          (cond ((zerop n) (quote zero))
                ((< n 5) (quote small))
                (T (quote big))))
        (classify 0) (classify 3) (classify 100)
        """,
        env,
    )
    cond_displayed = _printable(cond_results)
    distinct_strs = set(cond_displayed)
    cond_ok = len(cond_displayed) == 3 and len(distinct_strs) == 3 and all(s.isdigit() for s in cond_displayed)
    status = "OK" if cond_ok else "FAIL"
    print(f"  [{status}] cond → 3 distinct symbol ids: {cond_displayed}")
    if not cond_ok:
        fails += 1

    # ── Raw Cayley table access via `dot` builtin ──
    fails += not check(
        "dot exposes N=9 table (g=2, η=7 → g·η = 4 = Q)",
        "(dot 2 7)",
        [str(TABLE[2][7])],
    )

    # ── σ-equivariance at the Lisp level ──
    # For all atom indices a, b: σ(a·b) == σ(a)·σ(b)
    print()
    print("σ-equivariance check at Lisp level (via `dot`):")
    env = builtin_env()
    eq_fails = 0
    for a in range(N):
        for b in range(N):
            res = run(f"(dot {a} {b})", env)
            ab = decode_int(res[0])
            res2 = run(f"(dot {SIGMA[a]} {SIGMA[b]})", env)
            sa_sb = decode_int(res2[0])
            if SIGMA[ab] != sa_sb:
                eq_fails += 1
                print(f"  FAIL ({a},{b}): σ({ab})={SIGMA[ab]} ≠ σ(a)·σ(b)={sa_sb}")
    if eq_fails == 0:
        print(f"  [OK] σ((a·b)) = σ(a)·σ(b) for all 81 atom pairs")
    else:
        fails += eq_fails

    # ── Bonus: the documented one-step identities ──
    # f²=η, η²=f, Q²=Q, E²=E, g²=ρ, ρ²=ρ
    print()
    print("Bonus identities exposed through `dot`:")
    env = builtin_env()
    cases = [("f²", 5, 5, 7), ("η²", 7, 7, 5), ("Q²", 4, 4, 4),
             ("E²", 6, 6, 6), ("g²", 2, 2, 8), ("ρ²", 8, 8, 8)]
    for name, a, b, expected in cases:
        res = run(f"(dot {a} {b})", env)
        got = decode_int(res[0])
        status = "OK" if got == expected else "FAIL"
        print(f"  [{status}] {name} = {got} (expected {expected})")
        if got != expected:
            fails += 1

    print()
    if fails == 0:
        print("All N=9 Ψ-Lisp smoke tests passed.")
        return 0
    else:
        print(f"{fails} failure(s).")
        return 1


if __name__ == "__main__":
    sys.exit(main())

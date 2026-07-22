#!/usr/bin/env python3
"""
Factorial as a self-contained Ψ∗/N=9 term using the Z fixed-point.

Demonstrates that with the minimal λ-extension in psi_star_n9_lam (Lam,
Var, Closure, Prim), recursion lives entirely inside the term — not in
the host language's call stack. This is the prerequisite for Futamura
projections (specialize eval against a program → recursive output term)
and for compilation to a host-free runtime.

The Z combinator (call-by-value Y) is built from Lam/Var only:

  Z = λf. (λx. f (λv. (x x) v))
         (λx. f (λv. (x x) v))

Factorial:

  fact-body = λself. λn. if (zero? n) 1 (n * (self (n-1)))
  fact      = Z fact-body

Every node in `fact_term` below is a Lam, Var, App, Prim, or `nat`.
There is no Python `Function` object, no defun, no Lisp environment.
The whole term can be serialized, partial-evaluated, or shipped to a
host-free runtime (modulo replacing Prim with Q-chain arithmetic).
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_star_n9_lam import (
    App, Lam, Var, Prim, psi_eval, term_str, nat, to_nat,
)

# ═══════════════════════════════════════════════════════════════════════
# Z combinator (call-by-value Y) as a pure Lam/Var/App term
# ═══════════════════════════════════════════════════════════════════════
#
# de Bruijn:
#   Z = λ f.        # f = #0 here
#         (λ x.     # x = #0; f = #1 inside this lambda
#            (Var(1)            # = f
#             (λ v.             # v = #0; x = #1; f = #2
#                ((Var(1) Var(1)) Var(0))   # (x x) v
#             )))
#         (λ x. ... )           # same body
#
# The "η-expanded" inner lambda (λv. (x x) v) is what makes this Z (CBV)
# rather than the divergent CBN Y.

_inner = Lam(App(App(Var(1), Var(1)), Var(0)))   # λv. (x x) v
_outer = Lam(App(Var(1), _inner))                # λx. f (λv. (x x) v)
Z = Lam(App(_outer, _outer))                     # λf. (above) (above)


# ═══════════════════════════════════════════════════════════════════════
# Factorial body: a function from `self` to a function from `n` to result
# ═══════════════════════════════════════════════════════════════════════
#
# de Bruijn:
#   λ self.        # self = #0
#     λ n.         # n = #0; self = #1
#       if (zero? n)
#          1
#          (n * (self (n - 1)))

fact_body = Lam(Lam(
    Prim("if", (
        Prim("zero?", (Var(0),)),                      # n == 0 ?
        nat(1),                                         # then 1
        Prim("mul", (                                   # else n * (self (n-1))
            Var(0),
            App(Var(1),
                Prim("sub", (Var(0), nat(1)))),
        )),
    ))
))

# Factorial as a closed term — Y-bound recursion at the term level.
fact_term = App(Z, fact_body)


def main() -> int:
    print("Factorial as a self-contained Ψ∗/N=9 term")
    print()
    print(f"  Z combinator    : {term_str(Z, 40)}")
    print(f"  factorial body  : {term_str(fact_body, 40)}")
    print(f"  factorial term  : (Z fact-body)")
    print()

    # The crucial demonstration: feed `App(fact_term, nat(n))` to psi_eval,
    # nothing more. No Function objects, no defun env, no host-language
    # recursion at the Lisp level — the only host work is psi_eval
    # itself (and the Prim arithmetic helpers).
    cases = [(0, 1), (1, 1), (2, 2), (3, 6), (4, 24), (5, 120),
             (6, 720), (7, 5040), (8, 40320), (10, 3628800)]

    fails = 0
    print(f"  {'n':>3} {'fact(n)':>10} {'expected':>10} {'status':>8}")
    print(f"  {'─'*3} {'─'*10} {'─'*10} {'─'*8}")
    for n, expected in cases:
        result = psi_eval(App(fact_term, nat(n)))
        got = to_nat(result)
        status = "OK" if got == expected else "FAIL"
        if got != expected:
            fails += 1
        print(f"  {n:>3} {got!s:>10} {expected!s:>10} {status:>8}")

    print()
    if fails == 0:
        print("Factorial works as a closed Ψ∗/N=9 term using term-level Y.")
        print()
        print("What this means:")
        print("  • The recursion lives in the *term*, not in Python's call stack.")
        print("  • The term can be specialized (1st Futamura) — partial-")
        print("    evaluating `(Z fact-body)` against a literal n unrolls it.")
        print("  • A host-free runtime (Rust/C) only needs to implement")
        print("    psi_eval + the Prim table; no closure-from-host machinery.")
        print()
        print("Open work to remove the Prim escape hatch entirely:")
        print("  • Encode `add`, `sub`, `mul`, `zero?` as Q-chain manipulations")
        print("    using only Q, E, ρ. Each becomes its own Y-bound term.")
        print("    `add` is the easy starter (iterated succ); `mul` builds on it.")
        return 0
    else:
        print(f"{fails} failure(s).")
        return 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""
Ψ∗ over the N=9 canonical-witness Lisp substrate.

The 9-element magma documented in scripts/CANONICAL_LISP_N9.md, with
σ = (f η)(Q E) realised internally by ρ. The term algebra is the same
shape as DistinctionStructures/psi_star.py over Ψ₁₆ᶠ; only the table,
atom indices, and the absence of a Y atom differ.

Atom mapping (canonical N=9 indices on the right):
  TOP   = 1   z₂   T  / true  / ground       (absorber)
  BOT   = 0   z₁   NIL / false / empty list  (absorber)
  G_ENC = 2   g    cons
  TAU   = 3   τ    atom-tester (indicator classifier)
  Q     = 4   Q    quote
  F_ENC = 5   f    car
  E     = 6   E    eval
  ETA   = 7   η    cdr
  RHO   = 8   ρ    cond / σ-implementer

Note: the absorber roles are swapped relative to Ψ₁₆ᶠ. There TOP=0=T
and BOT=1=NIL; here z₁=0=NIL and z₂=1=T. We expose names so that
LISP_T = TOP and LISP_NIL = BOT continue to mean truth and nil.

There is no Y atom in this substrate. Recursion is handled by the
Lisp frontend's Python call stack (Y_COMB = None). The psi_eval
machinery skips the Y branch when the atom is absent.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

# ═══════════════════════════════════════════════════════════════════════
# N=9 Cayley table (from scripts/n9_lisp_natural_duality_result.json)
# ═══════════════════════════════════════════════════════════════════════
#
# Rows/cols are indexed 0..8 = z₁,z₂,g,τ,Q,f,E,η,ρ.

TABLE = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0],  # z₁ (NIL absorber)
    [1, 1, 1, 1, 1, 1, 1, 1, 1],  # z₂ (T  absorber)
    [8, 8, 8, 2, 7, 6, 5, 4, 2],  # g  (cons)
    [0, 1, 0, 1, 0, 0, 0, 0, 0],  # τ  (indicator classifier)
    [1, 0, 3, 2, 4, 8, 6, 5, 7],  # Q  (quote)
    [3, 3, 4, 6, 5, 7, 2, 2, 6],  # f  (car)
    [1, 0, 3, 2, 4, 7, 6, 8, 5],  # E  (eval)
    [3, 3, 6, 4, 2, 2, 7, 5, 4],  # η  (cdr)
    [0, 8, 2, 3, 6, 7, 4, 5, 8],  # ρ  (cond / σ-implementer)
]

N = 9

BOT = 0      # z₁  NIL / false / empty list
TOP = 1      # z₂  T   / true  / ground
G_ENC = 2    # g   cons
TAU = 3      # τ   atom-tester
Q = 4        # Q   quote (lazy constructor / successor)
F_ENC = 5    # f   car (fst projection)
E = 6        # E   eval (destructor / predecessor)
ETA = 7      # η   cdr (snd projection)
RHO = 8      # ρ   cond / structural branch

Y_COMB = None  # no Y atom in N=9 — recursion happens at the host level

NAMES = {
    0: "z₁", 1: "z₂", 2: "g", 3: "τ", 4: "Q",
    5: "f", 6: "E", 7: "η", 8: "ρ",
}

# σ on the carrier (from the same SAT model). σ = (f η)(Q E).
SIGMA = [0, 1, 2, 3, 6, 7, 4, 5, 8]


def dot(a: int, b: int) -> int:
    """N=9 binary operation."""
    return TABLE[a][b]


# ═══════════════════════════════════════════════════════════════════════
# Ψ∗ term representation
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class App:
    fun: "Term"
    arg: "Term"

Term = Union[int, App]


def term_str(t: Term, max_depth: int = 30) -> str:
    if max_depth <= 0:
        return "..."
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    return f"({term_str(t.fun, max_depth-1)} · {term_str(t.arg, max_depth-1)})"


# ═══════════════════════════════════════════════════════════════════════
# Naturals (Q as successor, ⊤ as zero)
# ═══════════════════════════════════════════════════════════════════════

def nat(n: int) -> Term:
    t: Term = TOP
    for _ in range(n):
        t = App(Q, t)
    return t


def to_nat(t: Term) -> int | None:
    n = 0
    while isinstance(t, App) and t.fun == Q:
        n += 1
        t = t.arg
    return n if t == TOP else None


def is_zero(t: Term) -> bool:
    return t == TOP


# ═══════════════════════════════════════════════════════════════════════
# Pairs (g curried; f extracts fst, η extracts snd)
# ═══════════════════════════════════════════════════════════════════════

def pair(a: Term, b: Term) -> Term:
    return App(App(G_ENC, a), b)


def fst(t: Term) -> Term | None:
    if isinstance(t, App) and isinstance(t.fun, App) and t.fun.fun == G_ENC:
        return t.fun.arg
    return None


def snd(t: Term) -> Term | None:
    if isinstance(t, App) and isinstance(t.fun, App) and t.fun.fun == G_ENC:
        return t.arg
    return None


# ═══════════════════════════════════════════════════════════════════════
# Ψ∗ evaluator — same semantics as DistinctionStructures/psi_star.py
# ═══════════════════════════════════════════════════════════════════════

class EvalError(Exception):
    pass


def psi_eval(t: Term, max_steps: int = 100000, _steps: list | None = None) -> Term:
    """Evaluate a Ψ∗ term over the N=9 substrate.

    Constructors:
      Q:  eval(App(Q, t)) = App(Q, t)             (Q freezes — lazy)
      g:  eval(App(g, t)) = App(g, eval(t))

    Destructors:
      E:  eval(App(E, App(Q, t)))                  = eval(t)
      f:  eval(App(f, App(App(g, a), b)))          = eval(a)
      η:  eval(App(η, App(App(g, a), b)))          = eval(b)

    Control:
      ρ:  eval(App(ρ, t)):
            v = eval(t)
            if v is atom    → eval(App(f, t))      f-path (base case)
            if v is App     → eval(App(g, t))      g-path (compound)

    Default:
      eval(atom)      = atom
      eval(App(a, b)) = dot(eval(a), eval(b))      (table fallback)
    """
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    fn, arg = t.fun, t.arg

    if fn == Q:
        return t

    if fn == G_ENC:
        return App(G_ENC, psi_eval(arg, max_steps, _steps))

    if fn == E:
        val = psi_eval(arg, max_steps, _steps)
        if isinstance(val, App) and val.fun == Q:
            return psi_eval(val.arg, max_steps, _steps)
        if isinstance(val, int):
            return dot(E, val)
        return App(E, val)

    if fn == F_ENC:
        val = psi_eval(arg, max_steps, _steps)
        first = fst(val)
        if first is not None:
            return psi_eval(first, max_steps, _steps)
        if isinstance(val, int):
            return dot(F_ENC, val)
        return App(F_ENC, val)

    if fn == ETA:
        val = psi_eval(arg, max_steps, _steps)
        second = snd(val)
        if second is not None:
            return psi_eval(second, max_steps, _steps)
        if isinstance(val, int):
            return dot(ETA, val)
        return App(ETA, val)

    if Y_COMB is not None and fn == Y_COMB:
        return App(Y_COMB, psi_eval(arg, max_steps, _steps))

    if fn == RHO:
        val = psi_eval(arg, max_steps, _steps)
        if isinstance(val, int):
            return psi_eval(App(F_ENC, arg), max_steps, _steps)
        else:
            return psi_eval(App(G_ENC, arg), max_steps, _steps)

    fn_val = psi_eval(fn, max_steps, _steps)
    arg_val = psi_eval(arg, max_steps, _steps)

    if isinstance(fn_val, int) and not isinstance(fn, int):
        return psi_eval(App(fn_val, arg_val), max_steps, _steps)

    if isinstance(fn_val, App) and fn_val.fun == G_ENC:
        return App(fn_val, arg_val)

    if isinstance(fn_val, int) and isinstance(arg_val, int):
        return dot(fn_val, arg_val)

    return App(fn_val, arg_val)


# ═══════════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════════

def _test_primitives():
    print("Ψ∗/N=9 primitive smoke-test")
    print(f"  atoms: TOP={TOP} BOT={BOT} g={G_ENC} τ={TAU} "
          f"Q={Q} f={F_ENC} E={E} η={ETA} ρ={RHO}")

    for n in range(5):
        t = nat(n)
        assert to_nat(t) == n, f"nat({n}) decode mismatch"
    print("  nat encode/decode: OK")

    for n in range(4):
        succ_n = psi_eval(App(Q, nat(n)))
        assert to_nat(succ_n) == n + 1, f"succ({n}) failed"
    print("  Q (lazy succ): OK")

    for n in range(1, 5):
        pred_n = psi_eval(App(E, nat(n)))
        assert to_nat(pred_n) == n - 1, f"pred({n}) failed"
    print("  E (pred via QE): OK")

    p = pair(nat(2), nat(3))
    a = psi_eval(App(F_ENC, p))
    b = psi_eval(App(ETA, p))
    assert to_nat(a) == 2 and to_nat(b) == 3, "fst/snd failed"
    print("  pair / f / η: OK")

    state = pair(pair(nat(3), nat(5)), nat(2))
    inner = psi_eval(App(F_ENC, state))
    c0 = psi_eval(App(F_ENC, inner))
    c1 = psi_eval(App(ETA, inner))
    pc = psi_eval(App(ETA, state))
    assert (to_nat(c0), to_nat(c1), to_nat(pc)) == (3, 5, 2), "nested pair failed"
    print("  nested pair (state encoding): OK")

    # ρ structural dispatch
    r_atom = psi_eval(App(RHO, TOP))
    r_comp = psi_eval(App(RHO, App(Q, TOP)))
    print(f"  ρ on atom    → {term_str(r_atom)}")
    print(f"  ρ on compound→ {term_str(r_comp)}")

    # σ-equivariance check at the atom level: SIGMA permutes the table
    for a in range(N):
        for b in range(N):
            assert SIGMA[TABLE[a][b]] == TABLE[SIGMA[a]][SIGMA[b]], \
                f"σ-equivariance failed at ({a},{b})"
    print("  σ-equivariance of TABLE: OK")

    print("All N=9 primitive tests passed.")


if __name__ == "__main__":
    _test_primitives()

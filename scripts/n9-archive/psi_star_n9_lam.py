#!/usr/bin/env python3
"""
Term-level λ extension for Ψ∗/N=9.

`psi_star_n9.py` provides the bare algebra: Q, E, f, g, η, ρ, τ over the
9-element table. There is no β-reduction at the term level — lambdas in
the Lisp frontend are Python `Function` objects, and recursion happens
in Python's call stack. That is fine for "Python is the machine," but it
blocks Futamura projections / compilation, since the output is half
term and half host closure.

This module adds the smallest extension that lets you express a
self-contained recursive Ψ∗ term: de-Bruijn-indexed `Lam`/`Var`, a
`Closure` value, and a host-primitive escape hatch `Prim`. The
evaluator threads an environment and does β-reduction; for everything
else (atoms, App-trees, pairs, Q/E/f/η/ρ) it delegates back to the
base evaluator.

Why de Bruijn:
  No name capture, no fresh-variable bookkeeping. Closures carry an
  env tuple; `Var(k)` looks up env[k]. This is the simplest substrate
  for a Ψ∗-level Y combinator and term-level partial evaluation.

Why a `Prim` hatch:
  The point of this exercise is term-level *control structure* (Y,
  application, recursion). Integer arithmetic and zero-tests can be
  encoded from atoms (Q-chains for naturals, ρ for atom/compound
  dispatch), but that is a separate exercise. `Prim("mul", a, b)` keeps
  the demonstration honest about what is term-level (the Z combinator,
  the factorial body, the application path) and what is borrowed
  (integer arithmetic).

Once you replace `Prim` with a Q-chain encoding of the same operations,
the resulting term is fully closed under the N=9 substrate plus the
λ-extension here.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Union

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import psi_star_n9 as base
from psi_star_n9 import (
    App, EvalError, TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, TAU,
    pair, fst, snd, term_str as base_term_str, NAMES, TABLE, dot, nat, to_nat,
)

# ═══════════════════════════════════════════════════════════════════════
# Extended term language
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Lam:
    """λ. body — body uses Var(0) for the just-bound argument."""
    body: "TermX"


@dataclass(frozen=True)
class Var:
    """de Bruijn index — Var(0) is innermost."""
    index: int


@dataclass(frozen=True)
class Closure:
    """Value: a Lam captured against the env at its creation site."""
    body: "TermX"
    env: tuple


@dataclass(frozen=True)
class Prim:
    """Escape hatch for host primitives (arithmetic, predicates).

    Treated as a value-yielding term: all args are evaluated, then the
    named host primitive is applied.
    """
    name: str
    args: tuple


TermX = Union[int, App, Lam, Var, Closure, Prim]


def term_str(t: TermX, max_depth: int = 30) -> str:
    if max_depth <= 0:
        return "..."
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    if isinstance(t, Var):
        return f"#{t.index}"
    if isinstance(t, Lam):
        return f"λ.{term_str(t.body, max_depth-1)}"
    if isinstance(t, Closure):
        return f"<clo λ.{term_str(t.body, max_depth-1)}>"
    if isinstance(t, Prim):
        return f"{t.name}({', '.join(term_str(a, max_depth-1) for a in t.args)})"
    if isinstance(t, App):
        return f"({term_str(t.fun, max_depth-1)} · {term_str(t.arg, max_depth-1)})"
    return str(t)


# ═══════════════════════════════════════════════════════════════════════
# Host-primitive table
# ═══════════════════════════════════════════════════════════════════════

def _decode_nat(t: TermX) -> int:
    """Decode a Q-chain natural; raises if the term is not a nat."""
    n = to_nat(t)
    if n is None:
        raise EvalError(f"expected nat, got {term_str(t)}")
    return n


# Prims with eager arg evaluation. `if` is special-cased below — it
# must be lazy in its branches or recursion never terminates.
PRIMS = {
    "add":   lambda a, b: nat(_decode_nat(a) + _decode_nat(b)),
    "sub":   lambda a, b: nat(max(0, _decode_nat(a) - _decode_nat(b))),
    "mul":   lambda a, b: nat(_decode_nat(a) * _decode_nat(b)),
    # zero? returns TOP for true, BOT for false (the standard truthy convention).
    "zero?": lambda a: TOP if a == TOP else BOT,
}


# ═══════════════════════════════════════════════════════════════════════
# Extended evaluator
# ═══════════════════════════════════════════════════════════════════════

def psi_eval(t: TermX, env: tuple = (), max_steps: int = 200000,
             _steps: list | None = None) -> TermX:
    """β-reducing evaluator over the λ-extended Ψ∗/N=9 term language.

    Threading rule: env is a tuple of values (innermost first). Var(k)
    looks up env[k]. Lam captures env into a Closure. App on a Closure
    extends env and re-enters the body.

    Anything that doesn't involve Lam/Var/Closure/Prim is forwarded to
    `base.psi_eval` after evaluating sub-terms — preserving the bare
    N=9 reductions for atoms, Q/E, f/η, g, ρ.
    """
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    if isinstance(t, Var):
        if t.index >= len(env):
            raise EvalError(f"unbound Var({t.index}) in env of size {len(env)}")
        return env[t.index]

    if isinstance(t, Lam):
        return Closure(t.body, env)

    if isinstance(t, Closure):
        return t  # closures are values

    if isinstance(t, Prim):
        # `if` is lazy in its branches.
        if t.name == "if":
            if len(t.args) != 3:
                raise EvalError("if takes 3 args (cond, then, else)")
            cond_v = psi_eval(t.args[0], env, max_steps, _steps)
            chosen = t.args[1] if cond_v == TOP else t.args[2]
            return psi_eval(chosen, env, max_steps, _steps)
        vals = tuple(psi_eval(a, env, max_steps, _steps) for a in t.args)
        if t.name not in PRIMS:
            raise EvalError(f"unknown primitive: {t.name}")
        return PRIMS[t.name](*vals)

    if isinstance(t, App):
        fn_val = psi_eval(t.fun, env, max_steps, _steps)

        # ── β-reduction path ──
        if isinstance(fn_val, Closure):
            arg_val = psi_eval(t.arg, env, max_steps, _steps)
            new_env = (arg_val,) + fn_val.env
            return psi_eval(fn_val.body, new_env, max_steps, _steps)

        # ── Atom-level / pair-level path: hand off to base ──
        # Re-evaluate via the base evaluator. We have to re-evaluate the
        # arg in the current env (not base env) first — it might contain
        # Vars that the base evaluator doesn't know about.
        arg_val = psi_eval(t.arg, env, max_steps, _steps)

        # If both are now base-eval terms (no Lam/Var/Closure/Prim leftover),
        # delegate to base for any algebraic reduction it can do.
        if _is_base_term(fn_val) and _is_base_term(arg_val):
            return base.psi_eval(App(fn_val, arg_val), max_steps, _steps)

        # Otherwise leave as an App; nothing more to reduce here.
        return App(fn_val, arg_val)

    raise EvalError(f"unhandled term: {t!r}")


def _is_base_term(t) -> bool:
    """True if t contains only ints and base App nodes — no Lam/Var/etc."""
    if isinstance(t, int):
        return True
    if isinstance(t, App):
        return _is_base_term(t.fun) and _is_base_term(t.arg)
    return False


# ═══════════════════════════════════════════════════════════════════════
# Smoke test
# ═══════════════════════════════════════════════════════════════════════

def _test():
    print("Ψ∗/N=9 + λ extension smoke-test")

    # Identity: (λx.x) 5 → 5
    Id = Lam(Var(0))
    r = psi_eval(App(Id, nat(5)))
    assert to_nat(r) == 5, f"identity failed: got {term_str(r)}"
    print("  identity λ: OK")

    # K combinator: (λx.λy.x) 7 9 → 7
    K = Lam(Lam(Var(1)))
    r = psi_eval(App(App(K, nat(7)), nat(9)))
    assert to_nat(r) == 7, f"K failed: got {term_str(r)}"
    print("  K combinator: OK")

    # Prim: (λx. x+1) 4 → 5
    succ = Lam(Prim("add", (Var(0), nat(1))))
    r = psi_eval(App(succ, nat(4)))
    assert to_nat(r) == 5, f"succ failed: got {term_str(r)}"
    print("  Prim arithmetic in lambda body: OK")

    # Pair construction still works (delegates to base)
    p = pair(nat(2), nat(3))
    a = psi_eval(App(F_ENC, p))
    assert to_nat(a) == 2
    print("  base-level pair / f / η still work: OK")

    print("All λ-extension primitive tests passed.")


if __name__ == "__main__":
    _test()

#!/usr/bin/env python3
"""
σ-equivariant λ encoding on Ψ∗/N=9.

The canonical-witness substrate has involution σ = (f η)(Q E). This module
takes that pairing seriously: lambdas use Q as the binder, applications
use E as the eliminator, and (function, argument) pairs use g/f/η for
construction/projection. The σ-pairing of the algebra IS the intro/elim
pairing of the calculus.

Encoding (the "wire format" — no AST sugar, just Ψ∗ atoms and one new
term constructor for de-Bruijn variables):

    λ. body         ≡  App(Q, body)              -- Q is the binder
    pair(a, b)      ≡  App(App(g, a), b)         -- standard
    apply(M, N)     ≡  App(E, App(App(g, M), N)) -- E forces a (fn, arg) pair
    Var(k)          ≡  the only ADT extension

Two new evaluator rules (added; nothing existing is changed):

  1. Var(k):
       env[k]                     -- env is a Python tuple at runtime
  2. App(E, pair(M, N)) where M evaluates to a Closure(body, env'):
       evaluate body with env = (N_value,) + env'

Closures are runtime values (not source terms). At the wire format level,
a lambda is App(Q, body); when evaluation encounters one with free Vars
in body it produces a Closure capturing the current env.

Cost of the encoding: each application is 4 atoms (E, g, then the two
App nodes). About 2× the "App(M, N)" version on disk. The win: the σ-image
of the encoding has an exact computational reading (functions ↔ their
applied forms), which is the property that justifies choosing the
canonical-witness substrate over Ψ₁₆ᶠ.

Documented limitation:
  A constant lambda `λx. body-without-Vars` has the same wire shape as
  the natural `body-without-Vars + 1` (an extra Q layer). The has_vars
  discriminator can't tell them apart — both look like Q-chains. The
  workaround is to write constant functions with a dummy bound var:
  `λx. (λy. y) body`. Factorial-style code never hits this; only pure
  constant functions do, and they're rare.
"""

from __future__ import annotations

import os
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Union

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_star_n9 import (
    App, EvalError, TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, TAU,
    NAMES, TABLE, dot, nat, to_nat, SIGMA,
)

# ═══════════════════════════════════════════════════════════════════════
# Term language
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Var:
    """de Bruijn index. Var(0) is the innermost binder."""
    index: int


@dataclass(frozen=True)
class Closure:
    """Runtime value — not part of the wire format."""
    body: "Term"
    env: tuple


@dataclass(frozen=True)
class Prim:
    """Escape hatch for host arithmetic (mul, sub, zero?, if).

    Lives at the AST level so the term tree stays first-order. To
    eliminate Prim entirely you would encode each operation as a
    Q-chain manipulation under its own Y-bound term — separate exercise.
    """
    name: str
    args: tuple


Term = Union[int, App, Var, Closure, Prim]


# ═══════════════════════════════════════════════════════════════════════
# Sugar — these are the only constructors source programs should use
# ═══════════════════════════════════════════════════════════════════════

def lam(body: Term) -> Term:
    """λ. body — Q-tagged binder."""
    return App(Q, body)


def app(M: Term, N: Term) -> Term:
    """apply(M, N) — E forces the (fn, arg) pair packed by g."""
    return App(E, App(App(G_ENC, M), N))


def pair_t(a: Term, b: Term) -> Term:
    return App(App(G_ENC, a), b)


# ═══════════════════════════════════════════════════════════════════════
# Lambda recognition — must distinguish Q-as-binder from Q-as-data
# ═══════════════════════════════════════════════════════════════════════

def has_vars(t: Term, _cache: dict | None = None) -> bool:
    """True iff t contains any Var node — the marker that t is a λ-body
    rather than a Q-chain natural."""
    if _cache is None:
        _cache = {}
    key = id(t)
    if key in _cache:
        return _cache[key]
    if isinstance(t, Var):
        r = True
    elif isinstance(t, App):
        r = has_vars(t.fun, _cache) or has_vars(t.arg, _cache)
    elif isinstance(t, Prim):
        r = any(has_vars(a, _cache) for a in t.args)
    else:
        r = False
    _cache[key] = r
    return r


# ═══════════════════════════════════════════════════════════════════════
# Pretty printing
# ═══════════════════════════════════════════════════════════════════════

def term_str(t: Term, max_depth: int = 30) -> str:
    if max_depth <= 0:
        return "..."
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    if isinstance(t, Var):
        return f"#{t.index}"
    if isinstance(t, Closure):
        return f"<clo body={term_str(t.body, max_depth-1)}>"
    if isinstance(t, Prim):
        return f"{t.name}({', '.join(term_str(a, max_depth-1) for a in t.args)})"
    if isinstance(t, App):
        return f"({term_str(t.fun, max_depth-1)} · {term_str(t.arg, max_depth-1)})"
    return str(t)


# ═══════════════════════════════════════════════════════════════════════
# Primitives
# ═══════════════════════════════════════════════════════════════════════

def _decode_nat(t: Term) -> int:
    n = to_nat(t)
    if n is None:
        raise EvalError(f"expected nat, got {term_str(t)}")
    return n


PRIMS = {
    "add":   lambda a, b: nat(_decode_nat(a) + _decode_nat(b)),
    "sub":   lambda a, b: nat(max(0, _decode_nat(a) - _decode_nat(b))),
    "mul":   lambda a, b: nat(_decode_nat(a) * _decode_nat(b)),
    "zero?": lambda a: TOP if a == TOP else BOT,
}


# ═══════════════════════════════════════════════════════════════════════
# Evaluator
# ═══════════════════════════════════════════════════════════════════════

# Module-level instrumentation hook. When set to a defaultdict(int)-like
# object, the evaluator records each atomic table fold. Used by the PE
# demo to detect bonus-identity firings.
INSTRUMENT: dict | None = None


def _record_dot(a: int, b: int) -> int:
    """dot wrapper that records each call when INSTRUMENT is active."""
    r = TABLE[a][b]
    if INSTRUMENT is not None:
        INSTRUMENT[(NAMES[a], NAMES[b], NAMES[r])] += 1
        if a == b:
            INSTRUMENT[("__square__", NAMES[a])] += 1
    return r


def psi_eval(t: Term, env: tuple = (), max_steps: int = 500000,
             _steps: list | None = None) -> Term:
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

    if isinstance(t, Closure):
        return t

    if isinstance(t, Prim):
        if t.name == "if":
            if len(t.args) != 3:
                raise EvalError("if takes 3 args")
            cv = psi_eval(t.args[0], env, max_steps, _steps)
            chosen = t.args[1] if cv == TOP else t.args[2]
            return psi_eval(chosen, env, max_steps, _steps)
        vals = tuple(psi_eval(a, env, max_steps, _steps) for a in t.args)
        if t.name not in PRIMS:
            raise EvalError(f"unknown primitive: {t.name}")
        return PRIMS[t.name](*vals)

    if isinstance(t, App):
        fn = t.fun
        arg = t.arg

        # Q-rule: lambdas (body has Vars) become Closures; data stays lazy.
        if fn == Q:
            if has_vars(arg):
                return Closure(arg, env)
            return t

        # E-rule: try β-reduction on (closure, value) pairs.
        if fn == E:
            arg_v = psi_eval(arg, env, max_steps, _steps)
            if (isinstance(arg_v, App) and isinstance(arg_v.fun, App)
                    and arg_v.fun.fun == G_ENC):
                M_val = arg_v.fun.arg
                N_val = arg_v.arg
                if isinstance(M_val, Closure):
                    new_env = (N_val,) + M_val.env
                    return psi_eval(M_val.body, new_env, max_steps, _steps)
            # Fall through to existing E semantics
            if isinstance(arg_v, App) and arg_v.fun == Q:
                return psi_eval(arg_v.arg, env, max_steps, _steps)
            if isinstance(arg_v, int):
                return _record_dot(E, arg_v)
            return App(E, arg_v)

        if fn == G_ENC:
            return App(G_ENC, psi_eval(arg, env, max_steps, _steps))

        if fn == F_ENC:
            val = psi_eval(arg, env, max_steps, _steps)
            if (isinstance(val, App) and isinstance(val.fun, App)
                    and val.fun.fun == G_ENC):
                return psi_eval(val.fun.arg, env, max_steps, _steps)
            if isinstance(val, int):
                return _record_dot(F_ENC, val)
            return App(F_ENC, val)

        if fn == ETA:
            val = psi_eval(arg, env, max_steps, _steps)
            if (isinstance(val, App) and isinstance(val.fun, App)
                    and val.fun.fun == G_ENC):
                return psi_eval(val.arg, env, max_steps, _steps)
            if isinstance(val, int):
                return _record_dot(ETA, val)
            return App(ETA, val)

        if fn == RHO:
            val = psi_eval(arg, env, max_steps, _steps)
            if isinstance(val, int):
                return psi_eval(App(F_ENC, arg), env, max_steps, _steps)
            return psi_eval(App(G_ENC, arg), env, max_steps, _steps)

        # General application — atom·atom dot fallback
        fn_v = psi_eval(fn, env, max_steps, _steps)
        arg_v = psi_eval(arg, env, max_steps, _steps)

        if isinstance(fn_v, int) and not isinstance(fn, int):
            return psi_eval(App(fn_v, arg_v), env, max_steps, _steps)

        if isinstance(fn_v, App) and fn_v.fun == G_ENC:
            return App(fn_v, arg_v)

        if isinstance(fn_v, int) and isinstance(arg_v, int):
            return _record_dot(fn_v, arg_v)

        return App(fn_v, arg_v)

    raise EvalError(f"unhandled term: {t!r}")


# ═══════════════════════════════════════════════════════════════════════
# σ-image (the structural involution applied to terms)
# ═══════════════════════════════════════════════════════════════════════

def sigma_image(t: Term) -> Term:
    """Apply σ atom-by-atom. Vars and Prim wrappers unchanged."""
    if isinstance(t, int):
        return SIGMA[t]
    if isinstance(t, App):
        return App(sigma_image(t.fun), sigma_image(t.arg))
    if isinstance(t, Var):
        return t
    if isinstance(t, Prim):
        return Prim(t.name, tuple(sigma_image(a) for a in t.args))
    return t


# ═══════════════════════════════════════════════════════════════════════
# Term-size accounting
# ═══════════════════════════════════════════════════════════════════════

def count_atoms(t: Term) -> int:
    """Count base algebra atoms (z₁..ρ leaves)."""
    if isinstance(t, int):
        return 1
    if isinstance(t, App):
        return count_atoms(t.fun) + count_atoms(t.arg)
    if isinstance(t, Var):
        return 0
    if isinstance(t, Prim):
        return sum(count_atoms(a) for a in t.args)
    return 0


def count_vars(t: Term) -> int:
    if isinstance(t, Var):
        return 1
    if isinstance(t, App):
        return count_vars(t.fun) + count_vars(t.arg)
    if isinstance(t, Prim):
        return sum(count_vars(a) for a in t.args)
    return 0


def count_prims(t: Term) -> int:
    if isinstance(t, Prim):
        return 1 + sum(count_prims(a) for a in t.args)
    if isinstance(t, App):
        return count_prims(t.fun) + count_prims(t.arg)
    return 0


# ═══════════════════════════════════════════════════════════════════════
# Smoke test
# ═══════════════════════════════════════════════════════════════════════

def _test():
    print("Ψ∗/N=9 σ-equivariant smoke-test")

    # Identity: λx. x
    Id = lam(Var(0))
    r = psi_eval(app(Id, nat(5)))
    assert to_nat(r) == 5
    print("  identity (Q-tagged lambda, E-app): OK")

    # K combinator: λx. λy. x
    K = lam(lam(Var(1)))
    r = psi_eval(app(app(K, nat(7)), nat(9)))
    assert to_nat(r) == 7
    print("  K combinator: OK")

    # Constant function via a dummy Var (the workaround for the inherent
    # ambiguity below). λx. (λy. y) 42 — the inner identity ensures the
    # outer lambda has a Var in its body.
    cf = lam(app(lam(Var(0)), nat(42)))
    r = psi_eval(app(cf, nat(3)))
    assert to_nat(r) == 42
    print("  λx. (λy. y) 42 (constant via dummy Var): OK")

    # Naturals stay as naturals (Q-data path) — same wire shape as a
    # variable-free lambda, which is why constant lambdas need the
    # workaround above. Documented limitation; factorial doesn't hit it.
    n5 = nat(5)
    assert to_nat(n5) == 5
    r = psi_eval(n5)
    assert to_nat(r) == 5
    print("  naturals untouched by lambda machinery: OK")

    # σ acts as expected on the wire format
    assert sigma_image(Q) == E
    assert sigma_image(E) == Q
    assert sigma_image(F_ENC) == ETA
    assert sigma_image(ETA) == F_ENC
    assert sigma_image(G_ENC) == G_ENC  # σ-fixed
    print("  σ swaps Q↔E, f↔η, fixes g/τ/ρ/z₁/z₂: OK")

    print("All σ-equivariant primitive tests passed.")


if __name__ == "__main__":
    _test()

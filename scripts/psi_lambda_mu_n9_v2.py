#!/usr/bin/env python3
"""
λμμ̃-on-N=9 v2: polarity-neutral cut form + position-swapping σ̂.

Two changes from psi_lambda_mu_n9.py (the v1 prototype):

1. POLARITY-NEUTRAL CUT FORM
   v1 used cut(M, N) = App(E, App(App(g, M), N)). The outer E is
   polarity-laden — under σ̂ it becomes Q, freezing the cut into a
   non-reducing value.

   v2 uses cut(M, N) = App(ρ, App(App(g, M), N)). Both ρ and g are
   σ-fixed in the N=9 algebra, so σ̂(cut) is structurally the same cut.
   The reduction trigger (ρ on a g-pair) is itself σ-symmetric.

2. POSITION-SWAPPING σ̂ ON CUTS
   In Curien-Herbelin the polarity involution τ swaps positions in
   cuts: τ(⟨v | e⟩) = ⟨τ(e) | τ(v)⟩. This is required for ⟨λ | _⟩
   (β-redex) to map under τ to ⟨_ | μ̃⟩ (μ̃-redex). v1's σ̂ recursed
   structurally through App without distinguishing cuts; v2 detects
   the cut shape and swaps M, N.

Together these two changes mean: the σ̂-image of a closed term built
from {Lam, CoLam, Var, CoVar, cut} is itself a closed term in the
same language with binders flipped, σ-paired atoms swapped, and cut
positions exchanged. The substrate's σ then becomes operational on
this fragment in the way the polarity involution requires.

What this v2 does NOT yet handle:
  - Top-level "halt" continuation. Atoms produced by CBV reduction
    don't have a σ-symmetric counterpart in the dual reduction
    (which produces CoClosures). Comparing atom outputs across σ̂
    requires a top-level termination convention we haven't added.
    This is why we test σ̂-commutation on values (Closures) rather
    than on observable outputs.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from typing import Union

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_star_n9 import (
    App, EvalError, TOP, BOT, Q, E, F_ENC, G_ENC, ETA, RHO, TAU,
    NAMES, TABLE, dot, nat, to_nat, SIGMA,
)

# ═══════════════════════════════════════════════════════════════════════
# AST
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Var:
    """Value variable (de Bruijn). Bound by Lam."""
    index: int


@dataclass(frozen=True)
class CoVar:
    """Continuation variable (de Bruijn). Bound by CoLam."""
    index: int


@dataclass(frozen=True)
class Lam:
    """λ. body — value binder. Wire form: still App(Q, body) at the
    encoding level if you want one; we use the AST node here for
    clarity and to avoid ambiguity with naturals."""
    body: "Term"


@dataclass(frozen=True)
class CoLam:
    """μ̃. body — continuation binder."""
    body: "Term"


@dataclass(frozen=True)
class Closure:
    body: "Term"
    venv: tuple
    kenv: tuple


@dataclass(frozen=True)
class CoClosure:
    body: "Term"
    venv: tuple
    kenv: tuple


Term = Union[int, App, Var, CoVar, Lam, CoLam, Closure, CoClosure]


# ═══════════════════════════════════════════════════════════════════════
# Sugar — polarity-neutral cut via ρ-wrapped g-pair
# ═══════════════════════════════════════════════════════════════════════

def lam(body: Term) -> Term:
    return Lam(body)


def colam(body: Term) -> Term:
    return CoLam(body)


def cut(M: Term, N: Term) -> Term:
    """⟨M | N⟩ — polarity-neutral. Both ρ and g are σ-fixed, so
    σ̂(cut) keeps the same wire shape (with positions swapped)."""
    return App(RHO, App(App(G_ENC, M), N))


def pair_t(a: Term, b: Term) -> Term:
    """Bare g-pair construction (data, not a cut)."""
    return App(App(G_ENC, a), b)


def is_cut_shape(t) -> bool:
    return (isinstance(t, App) and t.fun == RHO
            and isinstance(t.arg, App) and isinstance(t.arg.fun, App)
            and t.arg.fun.fun == G_ENC)


def cut_args(t) -> tuple:
    """Extract (M, N) from a cut-shaped term."""
    return (t.arg.fun.arg, t.arg.arg)


# ═══════════════════════════════════════════════════════════════════════
# Pretty printing
# ═══════════════════════════════════════════════════════════════════════

def term_str(t: Term, max_depth: int = 30) -> str:
    if max_depth <= 0:
        return "..."
    if isinstance(t, int):
        return NAMES.get(t, str(t))
    if isinstance(t, Var):
        return f"#v{t.index}"
    if isinstance(t, CoVar):
        return f"#k{t.index}"
    if isinstance(t, Lam):
        return f"λ.{term_str(t.body, max_depth-1)}"
    if isinstance(t, CoLam):
        return f"μ̃.{term_str(t.body, max_depth-1)}"
    if isinstance(t, Closure):
        return f"⟨clo {term_str(t.body, max_depth-1)} |V|={len(t.venv)} |K|={len(t.kenv)}⟩"
    if isinstance(t, CoClosure):
        return f"⟨coclo {term_str(t.body, max_depth-1)} |V|={len(t.venv)} |K|={len(t.kenv)}⟩"
    if isinstance(t, App):
        if is_cut_shape(t):
            M, N = cut_args(t)
            return f"⟨{term_str(M, max_depth-1)} | {term_str(N, max_depth-1)}⟩"
        return f"({term_str(t.fun, max_depth-1)} · {term_str(t.arg, max_depth-1)})"
    return str(t)


# ═══════════════════════════════════════════════════════════════════════
# Evaluator
# ═══════════════════════════════════════════════════════════════════════

def psi_eval(t: Term, venv: tuple = (), kenv: tuple = (),
             max_steps: int = 1000000, _steps: list | None = None) -> Term:
    if _steps is None:
        _steps = [0]
    _steps[0] += 1
    if _steps[0] > max_steps:
        raise EvalError(f"Exceeded {max_steps} steps")

    if isinstance(t, int):
        return t

    if isinstance(t, Var):
        if t.index >= len(venv):
            raise EvalError(f"unbound Var({t.index}); venv={len(venv)}")
        return venv[t.index]

    if isinstance(t, CoVar):
        if t.index >= len(kenv):
            raise EvalError(f"unbound CoVar({t.index}); kenv={len(kenv)}")
        return kenv[t.index]

    if isinstance(t, Lam):
        return Closure(t.body, venv, kenv)

    if isinstance(t, CoLam):
        return CoClosure(t.body, venv, kenv)

    if isinstance(t, (Closure, CoClosure)):
        return t

    if isinstance(t, App):
        # ── Cut form: ρ on a g-pair ────────────────────────────────
        if t.fun == RHO and isinstance(t.arg, App) and isinstance(t.arg.fun, App) \
                and t.arg.fun.fun == G_ENC:
            M = t.arg.fun.arg
            N = t.arg.arg
            mv = psi_eval(M, venv, kenv, max_steps, _steps)
            nv = psi_eval(N, venv, kenv, max_steps, _steps)
            # β: M is a value-binder closure
            if isinstance(mv, Closure):
                return psi_eval(mv.body, (nv,) + mv.venv, mv.kenv,
                                max_steps, _steps)
            # μ̃: N is a continuation-binder closure
            if isinstance(nv, CoClosure):
                return psi_eval(nv.body, nv.venv, (mv,) + nv.kenv,
                                max_steps, _steps)
            # No redex — return the constructed pair (data)
            return App(RHO, App(App(G_ENC, mv), nv))

        # ── Inherited atom-level rules from psi_star_n9 ────────────
        if t.fun == Q:
            return t

        if t.fun == E:
            arg_v = psi_eval(t.arg, venv, kenv, max_steps, _steps)
            if isinstance(arg_v, App) and arg_v.fun == Q:
                return psi_eval(arg_v.arg, venv, kenv, max_steps, _steps)
            if isinstance(arg_v, int):
                return TABLE[E][arg_v]
            return App(E, arg_v)

        if t.fun == G_ENC:
            return App(G_ENC, psi_eval(t.arg, venv, kenv, max_steps, _steps))

        if t.fun == F_ENC:
            val = psi_eval(t.arg, venv, kenv, max_steps, _steps)
            if isinstance(val, App) and isinstance(val.fun, App) \
                    and val.fun.fun == G_ENC:
                return psi_eval(val.fun.arg, venv, kenv, max_steps, _steps)
            if isinstance(val, int):
                return TABLE[F_ENC][val]
            return App(F_ENC, val)

        if t.fun == ETA:
            val = psi_eval(t.arg, venv, kenv, max_steps, _steps)
            if isinstance(val, App) and isinstance(val.fun, App) \
                    and val.fun.fun == G_ENC:
                return psi_eval(val.arg, venv, kenv, max_steps, _steps)
            if isinstance(val, int):
                return TABLE[ETA][val]
            return App(ETA, val)

        if t.fun == RHO:
            # ρ on non-cut: existing structural branch
            val = psi_eval(t.arg, venv, kenv, max_steps, _steps)
            if isinstance(val, int):
                return psi_eval(App(F_ENC, t.arg), venv, kenv, max_steps, _steps)
            return psi_eval(App(G_ENC, t.arg), venv, kenv, max_steps, _steps)

        # General application
        fn_v = psi_eval(t.fun, venv, kenv, max_steps, _steps)
        arg_v = psi_eval(t.arg, venv, kenv, max_steps, _steps)
        if isinstance(fn_v, int) and not isinstance(t.fun, int):
            return psi_eval(App(fn_v, arg_v), venv, kenv, max_steps, _steps)
        if isinstance(fn_v, App) and fn_v.fun == G_ENC:
            return App(fn_v, arg_v)
        if isinstance(fn_v, int) and isinstance(arg_v, int):
            return TABLE[fn_v][arg_v]
        return App(fn_v, arg_v)

    raise EvalError(f"unhandled term: {t!r}")


# ═══════════════════════════════════════════════════════════════════════
# σ̂ — algebra σ + AST polarity swap + cut-position swap
# ═══════════════════════════════════════════════════════════════════════

def sigma_hat(t: Term) -> Term:
    """Apply the polarity involution.

    Atoms: σ permutation (Q↔E, f↔η, others fixed).
    AST:   Var↔CoVar, Lam↔CoLam, Closure↔CoClosure (with envs σ̂-mapped
           and venv↔kenv exchanged).
    Cuts:  ⟨M | N⟩ ↔ ⟨σ̂(N) | σ̂(M)⟩  — POSITIONS SWAP (Curien-Herbelin).
    """
    if isinstance(t, int):
        return SIGMA[t]
    if isinstance(t, Var):
        return CoVar(t.index)
    if isinstance(t, CoVar):
        return Var(t.index)
    if isinstance(t, Lam):
        return CoLam(sigma_hat(t.body))
    if isinstance(t, CoLam):
        return Lam(sigma_hat(t.body))
    if isinstance(t, Closure):
        return CoClosure(sigma_hat(t.body),
                         tuple(sigma_hat(v) for v in t.kenv),
                         tuple(sigma_hat(v) for v in t.venv))
    if isinstance(t, CoClosure):
        return Closure(sigma_hat(t.body),
                       tuple(sigma_hat(v) for v in t.kenv),
                       tuple(sigma_hat(v) for v in t.venv))
    if isinstance(t, App):
        if is_cut_shape(t):
            M, N = cut_args(t)
            # Position swap: σ̂(⟨M | N⟩) = ⟨σ̂(N) | σ̂(M)⟩
            return cut(sigma_hat(N), sigma_hat(M))
        return App(sigma_hat(t.fun), sigma_hat(t.arg))
    return t


def terms_equal(a: Term, b: Term) -> bool:
    """Structural equality."""
    if type(a) != type(b):
        return False
    if isinstance(a, int):
        return a == b
    if isinstance(a, App):
        return terms_equal(a.fun, b.fun) and terms_equal(a.arg, b.arg)
    if isinstance(a, (Var, CoVar)):
        return a.index == b.index
    if isinstance(a, (Lam, CoLam)):
        return terms_equal(a.body, b.body)
    if isinstance(a, (Closure, CoClosure)):
        return (terms_equal(a.body, b.body)
                and len(a.venv) == len(b.venv) and len(a.kenv) == len(b.kenv)
                and all(terms_equal(x, y) for x, y in zip(a.venv, b.venv))
                and all(terms_equal(x, y) for x, y in zip(a.kenv, b.kenv)))
    return a == b


# ═══════════════════════════════════════════════════════════════════════
# Smoke tests
# ═══════════════════════════════════════════════════════════════════════

def _test():
    print("v2 smoke test")

    # Identity: ⟨id | T⟩ → T
    Id = lam(Var(0))
    r = psi_eval(cut(Id, TOP))
    assert r == TOP, f"identity broken: {term_str(r)}"
    print("  ⟨id | T⟩ → T: OK")

    # K: ⟨⟨K | T⟩ | NIL⟩ → T
    K = lam(lam(Var(1)))
    r = psi_eval(cut(cut(K, TOP), BOT))
    assert r == TOP, f"K broken: {term_str(r)}"
    print("  ⟨⟨K | T⟩ | NIL⟩ → T: OK")

    # σ̂ on cut swaps positions
    sample = cut(Var(0), CoVar(1))
    sig = sigma_hat(sample)
    expected = cut(sigma_hat(CoVar(1)), sigma_hat(Var(0)))
    assert terms_equal(sig, expected), \
        f"cut σ̂ wrong: {term_str(sig)} vs {term_str(expected)}"
    print("  σ̂ swaps cut positions: OK")

    # σ̂² == id on cuts
    sig_sig = sigma_hat(sigma_hat(sample))
    assert terms_equal(sig_sig, sample), \
        f"σ̂² ≠ id: {term_str(sig_sig)} vs {term_str(sample)}"
    print("  σ̂²=id on cut shape: OK")

    print("v2 smoke OK.")


if __name__ == "__main__":
    _test()

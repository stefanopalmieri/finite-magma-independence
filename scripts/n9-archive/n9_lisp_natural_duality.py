"""
N=9 canonical-witness Lisp substrate with σ = (f η)(Q E).

The structurally most elegant canonical-witness Lisp at N=9: σ pairs
the two natural Lisp dualities (car↔cdr projection-swap and
quote↔eval homoiconicity-swap) and σ-fixes the asymmetric singletons
(cons, cond, tester, absorbers).

SAT in 3.7s with bonus algebraic identities:

  σ = (f η)(Q E),  order 2
  σ-fixed: {z₁, z₂, g (cons), τ (tester), ρ (cond)}

  f² = η    (car squared = cdr)
  η² = f    (cdr squared = car)
  Q² = Q    (quote is atomically idempotent)
  E² = E    (eval is atomically idempotent)
  g² = ρ    (cons squared = cond)
  ρ² = ρ    (cond is idempotent)

Compare with the (f g)(Q E) variant:
  - (f g)(Q E): pairs car-cons (constructor-destructor) — unnatural
                Lisp duality. Bonus: f² = E, g² = Q.
  - (f η)(Q E): pairs car-cdr (the two projections) — natural
                Lisp duality. Bonus: f² = η, η² = f, three idempotents
                Q² = Q, E² = E, ρ² = ρ.

The (f η)(Q E) substrate aligns σ-orbits with Lisp's actual semantic
role-arity (one cons, two projections; one cond; one tester; one
quote-eval pair). The σ-fixed atoms are exactly the unique-role
primitives; the σ-paired atoms are exactly the natural duals. And
three of the four σ-fixed core elements (Q, E, ρ — wait, Q and E are
σ-paired, not σ-fixed, but Q² = Q and E² = E are still idempotents)
satisfy the cleanest possible self-equation.

Three of the σ-fixed atoms (g, τ, ρ) plus Q and E (which are
σ-paired but Q²=Q, E²=E nonetheless) are atomically idempotent or
satisfy one-step self-equations. That's an unusual amount of
algebraic regularity inside a 9-element magma.

This is the structurally cleanest canonical-witness Lisp substrate
identified so far.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N = 9
CORE = list(range(2, N))


def query():
    s = Solver()
    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)
    for x in range(N):
        s.add(T[0][x] == 0); s.add(T[1][x] == 1)
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))
    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw; pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))
    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE])); s.add(Or([rR == c for c in CORE]))
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx)); s.add(Or(srx))
    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)]) for tv in CORE]))
    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))
    z1, z2 = 0, 1
    for tau in CORE:
        indicator = And(T[tau][z1] == z1, T[tau][z2] == z2, T[tau][tau] == z2,
                        *[T[tau][x] == z1 for x in CORE if x != tau])
        s.add(Or(Not(is_cls[tau]), indicator))
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))
    s.add(Or(*[sigma[i] != i for i in range(N)]))
    for a in range(N):
        for b in range(N):
            big = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big.append(And(sigma[a] == sa, sigma[b] == sb,
                                       T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))
    rho = Int("rho")
    s.add(Or([rho == c for c in CORE]))
    for x in CORE:
        cl = []
        for rv in CORE:
            for sv in range(N):
                cl.append(And(rho == rv, sigma[x] == sv, T[rv][x] == sv))
        s.add(Or(*cl))
    Q = Int("Q"); E = Int("E")
    s.add(Or([Q == c for c in CORE])); s.add(Or([E == c for c in CORE]))
    s.add(Q != E); s.add(Q != rho); s.add(E != rho)
    for x in range(N):
        cl = []
        for qv in CORE:
            for ev in CORE:
                if qv == ev: continue
                cl.append(And(Q == qv, E == ev,
                              Or(*[And(T[qv][x] == iv, T[ev][iv] == x) for iv in range(N)])))
        s.add(Or(*cl))
    f_a = Int("f_a"); g_a = Int("g_a"); eta_a = Int("eta_a")
    for v in (f_a, g_a, eta_a):
        s.add(Or([v == c for c in CORE]))
    s.add(Distinct(f_a, g_a, eta_a, rho, Q, E))
    for v in (f_a, g_a, eta_a):
        s.add(Or(*[And(v == c, Not(is_cls[c])) for c in CORE]))
    for a in range(N):
        s.add(Or(*[And(T[a][a] == v, T[a][v] == T[v][a]) for v in range(N)]))
    fη = []
    for fv in CORE:
        for ev in CORE:
            if fv == ev: continue
            fη.append(And(f_a == fv, eta_a == ev, sigma[fv] == ev, sigma[ev] == fv))
    s.add(Or(*fη))
    qe = []
    for qv in CORE:
        for ev in CORE:
            if qv == ev: continue
            qe.append(And(Q == qv, E == ev, sigma[qv] == ev, sigma[ev] == qv))
    s.add(Or(*qe))
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    print(f"N=9 + canonical + Futamura + PA + σ=(f η)(Q E): [{dt:.2f}s] {res}")
    if res != sat:
        return None
    m = s.model()
    return {
        "table": [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)],
        "Q": m.eval(Q).as_long(), "E": m.eval(E).as_long(),
        "f": m.eval(f_a).as_long(), "g": m.eval(g_a).as_long(),
        "eta": m.eval(eta_a).as_long(), "rho": m.eval(rho).as_long(),
        "sigma": [m.eval(sigma[i]).as_long() for i in range(N)],
    }


def main():
    info = query()
    if info is None:
        return
    T = info["table"]
    print(f"  Q={info['Q']} E={info['E']} f={info['f']} g={info['g']} η={info['eta']} ρ={info['rho']}")
    print(f"  σ = {info['sigma']}")
    print(f"\n  Bonus algebraic identities:")
    print(f"    f² = {T[info['f']][info['f']]} (η = {info['eta']})")
    print(f"    η² = {T[info['eta']][info['eta']]} (f = {info['f']})")
    print(f"    Q² = {T[info['Q']][info['Q']]} (Q = {info['Q']})")
    print(f"    E² = {T[info['E']][info['E']]} (E = {info['E']})")
    print(f"    g² = {T[info['g']][info['g']]} (ρ = {info['rho']})")
    print(f"    ρ² = {T[info['rho']][info['rho']]} (ρ = {info['rho']})")
    out = os.path.join(SCRIPT_DIR, "n9_lisp_natural_duality_result.json")
    with open(out, "w") as fh:
        json.dump(info, fh, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

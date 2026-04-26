"""
N=9 canonical-witness Lisp substrate with joint σ = (f g)(Q E).

Tests whether σ can simultaneously swap the constructor-destructor pair
(f=car ↔ g=cons) AND the homoiconicity pair (Q=quote ↔ E=eval) at the
atomic level. Result: SAT in 3.8s.

The SAT model has an unexpected algebraic resonance:

  σ = (f g)(Q E),  f² = E,  g² = Q

Z3 wasn't asked for the f² = E or g² = Q equations — they fall out of
the joint constraints. Combined with σ-equivariance, this makes the
two pairs structurally bound:

  σ swaps (f, g) and (Q, E).
  Squaring f gives E; squaring g gives Q. So the σ-orbit of f under
  squaring traverses {f, E, Q²=2, ...} and similarly for g. Specific
  algebraic identities tie the four named atoms into a coherent system.

Fixed by σ: η (cdr), ρ (cond), τ (the indicator classifier),
absorbers. The "asymmetric" Lisp roles — cdr (the un-σ-paired
projection), cond (the branch primitive), tester — sit outside the
duality, while car/cons and quote/eval sit inside it as the two
σ-paired pairs.

This is the structural commitment a "canonical-witness Lisp" would
make: the canonical symmetry binds the homoiconicity pair to the
constructor-destructor pair via a single involution, with f² = E and
g² = Q as algebraic consequences rather than imposed axioms.

Whether the resulting system is computationally useful is a separate
question — but algebraically, the substrate is structurally tighter
than Ψ₁₆ᶠ (which is rigid and has no such symmetry-binding).
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

    fg_clauses = []
    for fv in CORE:
        for gv in CORE:
            if fv == gv: continue
            fg_clauses.append(And(f_a == fv, g_a == gv, sigma[fv] == gv, sigma[gv] == fv))
    s.add(Or(*fg_clauses))
    qe_clauses = []
    for qv in CORE:
        for ev in CORE:
            if qv == ev: continue
            qe_clauses.append(And(Q == qv, E == ev, sigma[qv] == ev, sigma[ev] == qv))
    s.add(Or(*qe_clauses))

    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    print(f"N=9 + canonical + Futamura + PA + σ=(f g)(Q E): [{dt:.2f}s] {res}")
    if res != sat:
        return None
    m = s.model()
    Q_v = m.eval(Q).as_long(); E_v = m.eval(E).as_long()
    f_v = m.eval(f_a).as_long(); g_v = m.eval(g_a).as_long()
    eta_v = m.eval(eta_a).as_long(); rho_v = m.eval(rho).as_long()
    sig = [m.eval(sigma[i]).as_long() for i in range(N)]
    table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
    return {
        "table": table, "Q": Q_v, "E": E_v, "f": f_v, "g": g_v,
        "eta": eta_v, "rho": rho_v, "sigma": sig,
    }


def main():
    info = query()
    if info is None:
        return
    print(f"  Q={info['Q']} E={info['E']} f={info['f']} g={info['g']} η={info['eta']} ρ={info['rho']}")
    print(f"  σ = {info['sigma']}")
    T = info['table']
    print(f"  f² = {T[info['f']][info['f']]}; expect E = {info['E']}")
    print(f"  g² = {T[info['g']][info['g']]}; expect Q = {info['Q']}")
    out = os.path.join(SCRIPT_DIR, "n9_lisp_joint_swap_result.json")
    with open(out, "w") as fh:
        json.dump(info, fh, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

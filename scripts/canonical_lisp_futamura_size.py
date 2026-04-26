"""
Find minimum N for canonical-witness + Lisp atomic substrate that
supports Ψ-Lisp-style Futamura projections.

Futamura projections need partial evaluation, which needs efficient
atomic pair primitives (car, cons, cdr) so the partial evaluator can
traverse program ASTs without Church-encoding overhead.

Substrate atoms required:
  - 2 absorbers (z₁ = NIL, z₂ = T)
  - 2 indicator classifiers (canonical-witness P1)
  - ρ: σ-implementer + branch primitive (canonical-witness P2)
  - Q, E: quote/eval pair (homoiconicity backbone)
  - f, g, η: car, cons, cdr atomic pair primitives

Distinct non-classifier core elements: ρ, Q, E, f, g, η = 6.
Plus 2 indicator classifiers.
Total minimum: 8 core elements ⇒ N ≥ 10.

Also: ask whether σ symmetrically exchanges f ↔ η (the cons-cell
projection-swap, the natural Lisp dual). If SAT, we get a substrate
where the canonical-witness symmetry binds *three* dual pairs:

  σ swaps  τ₁ ↔ τ₂     (truth-predicate duality)
            Q  ↔ E      (quote/eval duality)
            f  ↔ η      (car/cdr projection duality)
            fixes z₁, z₂, ρ, g

That's the synthesis: a Lisp where canonical-witness symmetry
internalises every natural Lisp duality at once.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def build_solver(N):
    CORE = list(range(2, N))
    s = Solver()
    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)
    for x in range(N):
        s.add(T[0][x] == 0)
        s.add(T[1][x] == 1)
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))
    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx))
        s.add(Or(srx))

    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
               for tv in CORE]))

    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(cases))
        diffs = [T[a][x1] != T[a][x2]
                 for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))
    return s, T, sR, rR, is_cls, CORE


def add_indicator_classifiers(s, T, is_cls, CORE):
    z1, z2 = 0, 1
    for tau in CORE:
        indicator_pattern = And(
            T[tau][z1] == z1, T[tau][z2] == z2, T[tau][tau] == z2,
            *[T[tau][x] == z1 for x in CORE if x != tau],
        )
        s.add(Or(Not(is_cls[tau]), indicator_pattern))


def add_self_symmetric_aut(s, T, N, CORE):
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
        clauses = []
        for rv in CORE:
            for sv in range(N):
                clauses.append(And(rho == rv, sigma[x] == sv, T[rv][x] == sv))
        s.add(Or(*clauses))
    return sigma, rho


def add_QE(s, T, N, CORE, rho):
    Q = Int("Q_atom"); E = Int("E_atom")
    s.add(Or([Q == c for c in CORE]))
    s.add(Or([E == c for c in CORE]))
    s.add(Q != E)
    s.add(Q != rho); s.add(E != rho)
    for x in range(N):
        clauses = []
        for qv in CORE:
            for ev in CORE:
                if qv == ev: continue
                inner_cases = [And(T[qv][x] == iv, T[ev][iv] == x) for iv in range(N)]
                clauses.append(And(Q == qv, E == ev, Or(*inner_cases)))
        s.add(Or(*clauses))
    return Q, E


def add_pair_primitives(s, T, is_cls, CORE, rho, Q, E):
    """Three distinct named non-classifier atoms f (car), g (cons), η (cdr).
    Distinct from each other and from ρ, Q, E."""
    f_atom = Int("f_atom"); g_atom = Int("g_atom"); eta_atom = Int("eta_atom")
    for v in (f_atom, g_atom, eta_atom):
        s.add(Or([v == c for c in CORE]))
    s.add(Distinct(f_atom, g_atom, eta_atom, rho, Q, E))
    # All three must be non-classifiers
    for v in (f_atom, g_atom, eta_atom):
        not_cls = []
        for c in CORE:
            not_cls.append(And(v == c, Not(is_cls[c])))
        s.add(Or(*not_cls))
    return f_atom, g_atom, eta_atom


def query(N, time_budget=1200):
    s, T, sR, rR, is_cls, CORE = build_solver(N)
    add_indicator_classifiers(s, T, is_cls, CORE)
    sigma, rho = add_self_symmetric_aut(s, T, N, CORE)
    Q, E = add_QE(s, T, N, CORE, rho)
    f_atom, g_atom, eta_atom = add_pair_primitives(s, T, is_cls, CORE, rho, Q, E)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== N={N} (canonical + Ψ atoms ⊤,⊥,Q,E,f,g,η,ρ + indicator) ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.2f}s] UNSAT")
        return False, None
    if res == sat:
        m = s.model()
        Q_v = m.eval(Q).as_long(); E_v = m.eval(E).as_long()
        f_v = m.eval(f_atom).as_long(); g_v = m.eval(g_atom).as_long()
        eta_v = m.eval(eta_atom).as_long(); rho_v = m.eval(rho).as_long()
        sigma_v = [m.eval(sigma[i]).as_long() for i in range(N)]
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        cls = [y for y in CORE if all(table[y][x] in (0, 1) for x in CORE)]
        ncl = [y for y in CORE if all(table[y][x] not in (0, 1) for x in CORE)]
        print(f"  [{dt:.2f}s] SAT")
        print(f"    Q={Q_v}, E={E_v}, f={f_v}, g={g_v}, η={eta_v}, ρ={rho_v}")
        print(f"    cls={cls}, ncl={ncl}")
        print(f"    σ = {sigma_v}")
        # Check whether σ exchanges f ↔ η (cons-cell projection-swap)
        f_eta_swap = sigma_v[f_v] == eta_v and sigma_v[eta_v] == f_v
        print(f"    σ exchanges f ↔ η (car/cdr duality)? {f_eta_swap}")
        for row in table:
            print(f"    {row}")
        return True, {
            "table": table, "Q": Q_v, "E": E_v, "f": f_v, "g": g_v,
            "eta": eta_v, "rho": rho_v, "sigma": sigma_v,
            "cls": cls, "ncl": ncl, "f_eta_swap": f_eta_swap,
        }
    print(f"  [{dt:.2f}s] UNKNOWN/timeout")
    return None, None


def main():
    print("Minimum N for canonical-witness + Ψ-Lisp atomic substrate (Futamura-capable)\n")
    results = {}
    for N in range(8, 13):
        sat_, info = query(N)
        results[N] = {"sat": sat_, "info": info}
        print()
        if sat_:
            print(f"  → First SAT at N={N}; this is the minimum size for the substrate.")
            break
    out = os.path.join(SCRIPT_DIR, "canonical_lisp_futamura_size_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

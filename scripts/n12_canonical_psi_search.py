"""
Incremental N=12 search: canonical-witness + Ψ-Lisp axioms one at a time.

Starts from S+D+C + indicator classifiers + self-symmetric automorphism
(SAT at N=12 per scripts/n12_canonical_search.py). Adds Ψ-Lisp axioms
incrementally until one breaks compatibility:

  Step 1: QE — ∃ Q, E ∈ core distinct, with ∀x: E·(Q·x) = x.
          (The quote/eval section-retraction pair. Lisp's homoiconicity
          backbone.)
  Step 2: QE-distinct-from-canonical — Q, E ∉ {classifiers, σ-implementer}.
          (Q and E are independent of the canonical-witness machinery.)
  Step 3: Y-trivial — ∃ Y ∈ core distinct from previous, with Y·Y = Y
          (idempotent at the atom level — a weak shadow of the fixed-point
          axiom).
  Step 4: ρ-branch — ∃ ρ that's a non-classifier, distinct from previous.
          (Branching primitive exists.)

Each step tested independently and stacked. If a step is UNSAT, that's
where canonical-witness collides with Ψ-Lisp axioms.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N = 12
CORE = list(range(2, N))


def build_solver(constrain_R=None):
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
    if constrain_R == "strong":
        s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if constrain_R == "strong" and sv == rv:
                    continue
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
    return s, T, sR, rR, is_cls


def add_indicator_classifiers(s, T, is_cls):
    z1, z2 = 0, 1
    for tau in CORE:
        indicator_pattern = And(
            T[tau][z1] == z1, T[tau][z2] == z2, T[tau][tau] == z2,
            *[T[tau][x] == z1 for x in CORE if x != tau],
        )
        s.add(Or(Not(is_cls[tau]), indicator_pattern))


def add_self_symmetric_aut(s, T):
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


def add_QE(s, T):
    """Step 1: ∃ Q, E ∈ core, Q ≠ E, ∀x ∈ Fin(N): T[E][T[Q][x]] = x."""
    Q = Int("Q_atom"); E = Int("E_atom")
    s.add(Or([Q == c for c in CORE]))
    s.add(Or([E == c for c in CORE]))
    s.add(Q != E)
    for x in range(N):
        clauses = []
        for qv in CORE:
            for ev in CORE:
                if qv == ev: continue
                # T[ev][T[qv][x]] = x
                inner_cases = [And(T[qv][x] == iv, T[ev][iv] == x) for iv in range(N)]
                clauses.append(And(Q == qv, E == ev, Or(*inner_cases)))
        s.add(Or(*clauses))
    return Q, E


def add_QE_distinct_from_canonical(s, Q, E, rho):
    """Step 2: Q, E distinct from σ-implementer ρ. (Q, E are not the
    classifier-swap implementer.)"""
    s.add(Q != rho)
    s.add(E != rho)


def add_Y_idempotent(s, T, Q, E, rho):
    """Step 3: ∃ Y ∈ core distinct from Q, E, ρ, with Y·Y = Y."""
    Y = Int("Y_atom")
    s.add(Or([Y == c for c in CORE]))
    s.add(Y != Q); s.add(Y != E); s.add(Y != rho)
    clauses = []
    for yv in CORE:
        # T[yv][yv] == yv
        clauses.append(And(Y == yv, T[yv][yv] == yv))
    s.add(Or(*clauses))
    return Y


def add_rho_nonclassifier(s, T, is_cls, Q, E, rho_swap, Y):
    """Step 4: ∃ rho_branch ∈ core, non-classifier, distinct from previous."""
    rho_branch = Int("rho_branch")
    s.add(Or([rho_branch == c for c in CORE]))
    s.add(rho_branch != Q); s.add(rho_branch != E)
    s.add(rho_branch != rho_swap); s.add(rho_branch != Y)
    not_cls_clauses = []
    for rv in CORE:
        not_cls_clauses.append(And(rho_branch == rv, Not(is_cls[rv])))
    s.add(Or(*not_cls_clauses))
    return rho_branch


def add_power_associativity(s, T):
    """Step 5: ∀ a ∈ Fin(N): a · (a · a) = (a · a) · a (power-associativity).
    Weaker than full associativity (which is UNSAT for S+D+C). Holds in Ψ₁₆ᶠ."""
    for a in range(N):
        # T[a][T[a][a]] == T[T[a][a]][a]
        clauses = []
        for v in range(N):
            clauses.append(And(T[a][a] == v, T[a][v] == T[v][a]))
        s.add(Or(*clauses))


def add_universal_Y(s, T, Y_existing=None):
    """Step 6: ∃ Y ∈ core such that ∀ f ∈ core: Y · f = f · (Y · f).
    True fixed-point combinator at the atom level. Strong axiom; may
    collide with other constraints. If Y_existing is given (from step 3),
    enforce on that element."""
    if Y_existing is None:
        Y = Int("Y_universal")
        s.add(Or([Y == c for c in CORE]))
    else:
        Y = Y_existing
    for f in CORE:
        clauses = []
        for yv in CORE:
            for yfv in range(N):
                clauses.append(And(Y == yv, T[yv][f] == yfv, T[f][yfv] == yfv))
        s.add(Or(*clauses))
    return Y


def query(label, constrain_R, axiom_steps, time_budget=600):
    s, T, sR, rR, is_cls = build_solver(constrain_R)
    add_indicator_classifiers(s, T, is_cls)
    sigma, rho = add_self_symmetric_aut(s, T)
    Q = E = Y = rho_branch = None
    if axiom_steps >= 1:
        Q, E = add_QE(s, T)
    if axiom_steps >= 2:
        add_QE_distinct_from_canonical(s, Q, E, rho)
    if axiom_steps >= 3:
        Y = add_Y_idempotent(s, T, Q, E, rho)
    if axiom_steps >= 4:
        rho_branch = add_rho_nonclassifier(s, T, is_cls, Q, E, rho, Y)
    if axiom_steps >= 5:
        add_power_associativity(s, T)
    if axiom_steps >= 6:
        add_universal_Y(s, T, Y_existing=Y)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== {label}: N={N}, R={constrain_R}, axiom_steps={axiom_steps} ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.1f}s] UNSAT")
        return False, None
    if res == sat:
        m = s.model()
        info = {
            "Q": m.eval(Q).as_long() if Q is not None else None,
            "E": m.eval(E).as_long() if E is not None else None,
            "Y": m.eval(Y).as_long() if Y is not None else None,
            "rho_branch": m.eval(rho_branch).as_long() if rho_branch is not None else None,
            "rho_swap": m.eval(rho).as_long(),
            "sigma": [m.eval(sigma[i]).as_long() for i in range(N)],
            "sR": m.eval(sR).as_long(),
            "rR": m.eval(rR).as_long(),
        }
        print(f"  [{dt:.1f}s] SAT  Q={info['Q']}, E={info['E']}, "
              f"Y={info['Y']}, ρ_branch={info['rho_branch']}, "
              f"ρ_swap={info['rho_swap']}, σ={info['sigma']}")
        return True, info
    print(f"  [{dt:.1f}s] UNKNOWN/timeout")
    return None, None


def main():
    print(f"N=12 canonical-witness + Ψ axioms incremental search")
    print(f"Each step adds one more Ψ axiom; stop when UNSAT.\n")
    results = {}
    # Try only "any" R-regime initially (faster); promote to strong/weak if interesting.
    for steps in (5, 6):
        sat_, info = query(f"Step {steps}", None, steps)
        results[f"step_{steps}"] = {"sat": sat_, "info": info}
        print()
        if not sat_:
            print(f"  → Stopping: step {steps} is UNSAT.")
            break
    out = os.path.join(SCRIPT_DIR, "n12_canonical_psi_search_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()

"""
Rigidity search under strong R + nontrivial classifier on core + asymmetric
anchoring (s . z1 != z1).

Experiment B: adds to experiment A the requirement that the section s NOT
anchor at z1 (only the retraction r does). This breaks the s <-> r swap
symmetry at z1, which was the structural source of non-rigidity at N=6
under Experiment A.

Usage: python3 rigidity_search_strongR_asym.py <N>
"""

from __future__ import annotations

import itertools
import json
import os
import sys
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


# --- brute-force verification helpers ----------------------------------------

def check_absorbers(T, N):
    return all(T[0][x] == 0 and T[1][x] == 1 for x in range(N))

def check_extensional(T, N):
    return len({tuple(r) for r in T}) == N

def check_no_other_constant(T, N, CORE):
    for y in CORE:
        if all(T[y][x] == y for x in range(N)):
            return False
    return True

def check_R_strong_asym(T, CORE):
    """Strong R + asymmetric anchoring: s!=r, mutual inverse on core,
    r anchors at z1, s does NOT anchor at z1."""
    for s_ in CORE:
        for r_ in CORE:
            if s_ == r_: continue
            if T[r_][0] != 0: continue
            if T[s_][0] == 0: continue  # s must NOT anchor at z1
            ok = True
            for x in CORE:
                if T[r_][T[s_][x]] != x or T[s_][T[r_][x]] != x:
                    ok = False; break
            if ok: return True, (s_, r_)
    return False, None

def check_D_nontriv(T, N, CORE):
    classifiers, non_classifiers = [], []
    for y in CORE:
        v = [T[y][x] for x in CORE]
        if all(u in (0, 1) for u in v):
            classifiers.append(y)
        elif all(u not in (0, 1) for u in v):
            non_classifiers.append(y)
        else:
            return False, None
    if not non_classifiers:
        return False, None
    for tau in CORE:
        if all(T[tau][x] in (0, 1) for x in range(N)):
            core_img = {T[tau][x] for x in CORE}
            if len(core_img) >= 2:
                return True, tau
    return False, None

def check_H(T, CORE):
    for a, b, c in itertools.permutations(CORE, 3):
        if not all(T[b][x] in CORE for x in CORE): continue
        if not all(T[a][x] == T[c][T[b][x]] for x in CORE): continue
        if len({T[a][x] for x in CORE}) < 2: continue
        return True, (a, b, c)
    return False, None

def is_ok(T, N, CORE):
    if not check_absorbers(T, N): return False, "absorbers"
    if not check_extensional(T, N): return False, "ext"
    if not check_no_other_constant(T, N, CORE): return False, "const-row"
    okR, _ = check_R_strong_asym(T, CORE)
    if not okR: return False, "R_strong_asym"
    okD, _ = check_D_nontriv(T, N, CORE)
    if not okD: return False, "D_nontriv"
    okH, _ = check_H(T, CORE)
    if not okH: return False, "H"
    return True, None

def automorphisms(T, N):
    auts = []
    for sigma in itertools.permutations(range(N)):
        if all(sigma[T[a][b]] == T[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N)):
            auts.append(sigma)
    return auts


# --- Z3 encoding -------------------------------------------------------------

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

    # Strong R + asymmetric anchoring.
    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(sR != rR)

    # r anchors at z1.
    r0 = [And(rR == rv, T[rv][0] == 0) for rv in CORE]
    s.add(Or(r0))

    # s does NOT anchor at z1 -- the asymmetry.
    s_notanch = [And(sR == sv, T[sv][0] != 0) for sv in CORE]
    s.add(Or(s_notanch))

    # Mutual inverse on core.
    for x in CORE:
        clauses_rsx, clauses_srx = [], []
        for sv in CORE:
            for rv in CORE:
                if sv == rv: continue
                inner_s, inner_r = T[sv][x], T[rv][x]
                rs_cases, sr_cases = [], []
                for iv in range(N):
                    rs_cases.append(And(inner_s == iv, T[rv][iv] == x))
                    sr_cases.append(And(inner_r == iv, T[sv][iv] == x))
                clauses_rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                clauses_srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(clauses_rsx))
        s.add(Or(clauses_srx))

    # D + nontrivial classifier on core.
    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    tau_cases = []
    for tv in CORE:
        is_cls_full = And(*[Or(T[tv][x] == 0, T[tv][x] == 1)
                             for x in range(N)])
        nontriv = Or(*[T[tv][x1] != T[tv][x2]
                        for x1, x2 in itertools.combinations(CORE, 2)])
        tau_cases.append(And(is_cls_full, nontriv))
    s.add(Or(*tau_cases))

    # H.
    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            inner = T[b][x]
            cases = [And(inner == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(cases))
        diffs = [T[a][x1] != T[a][x2]
                 for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))

    # Non-trivial automorphism.
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
                        big.append(And(
                            sigma[a] == sa, sigma[b] == sb,
                            T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))

    return s, T, sigma, (sR, rR)


def run(N):
    CORE = list(range(2, N))
    JSON_PATH = os.path.join(SCRIPT_DIR, f"nonrigid_rdh_N{N}_strongR_asym.json")
    TXT_PATH = os.path.join(SCRIPT_DIR, f"rigidity_search_N{N}_strongR_asym_result.txt")

    t0 = time.time()
    print(f"=== Z3: non-rigid at N={N}, strong R + nontrivial-tau + asym anchoring ===")
    s, T, sigma, (sR, rR) = build_solver(N)
    print(f"(setup: {time.time() - t0:.2f}s)")
    ts = time.time()
    result = s.check()
    elapsed = time.time() - ts
    print(f"Z3: {result}  ({elapsed:.2f}s)")

    if result == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sig = [m.eval(sigma[i]).as_long() for i in range(N)]
        s_val = m.eval(sR).as_long()
        r_val = m.eval(rR).as_long()
        print("\nWitness:")
        print("    " + " ".join(str(c) for c in range(N)))
        for a in range(N):
            print(f"{a}:  " + " ".join(str(table[a][b]) for b in range(N)))
        print(f"sigma = {sig}")
        print(f"R witness: s = {s_val} (T[{s_val}][0] = {table[s_val][0]}), r = {r_val}")
        ok, reason = is_ok(table, N, CORE)
        print(f"Verification: {ok}, reason={reason}")
        auts = automorphisms(table, N)
        print(f"|Aut| = {len(auts)}")

        data = {
            "N": N, "cayley_table": table, "sigma": sig,
            "R_witness": {"s": s_val, "r": r_val},
            "automorphisms": [list(a_) for a_ in auts],
            "z3_runtime_seconds": elapsed,
            "constraint": "strong R (s != r) + nontrivial-tau + asym anchoring (s . z1 != z1)",
        }
        with open(JSON_PATH, "w") as f:
            json.dump(data, f, indent=2)
        print(f"Wrote {JSON_PATH}")

    elif result == unsat:
        print(f"UNSAT: rigidity forced at N={N}.")
        with open(TXT_PATH, "w") as f:
            f.write(f"UNSAT at N={N}, strong R + nontrivial-tau + asym anchoring\n")
            f.write(f"(z3 runtime: {elapsed:.2f}s)\n")
        print(f"Wrote {TXT_PATH}")
    else:
        print(f"Unknown: {result}")
        sys.exit(2)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    run(N)

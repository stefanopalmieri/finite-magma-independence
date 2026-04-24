"""
Test factorizations of D and H through A12 (core-preserving row).

  D_struct = (every core row all-in/all-out on core) ∧ (∃ full classifier τ)
  H_eq     = (∃ distinct a,b,c ∈ core with a(x)=c(b(x)) on core, |im(a)|≥2)
  A12      = ∃ y ∈ core with T[y][core] ⊆ core

Candidate theorems:
  (D-factor)   D ⇔ D_struct ∧ A12
  (H-factor)   H ⇔ H_eq ∧ A12

For each: run UNSAT checks in both directions at N=5 and N=6.
"""

from __future__ import annotations

import itertools
import time

from z3 import And, BoolVal, Distinct, Int, Not, Or, Solver, sat, unknown, unsat


N_VALUES = [5, 6]
TIMEOUT_MS = 120_000


def make_solver():
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    return s


def make_T(N):
    return [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]


def add_E2PM(s, T, N):
    CORE = list(range(2, N))
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


def pred_A12(T, N):
    CORE = list(range(2, N))
    return Or(*[And(*[Or(*[T[y][x] == cc for cc in CORE]) for x in CORE])
               for y in CORE])


def pred_D(T, N):
    CORE = list(range(2, N))
    dicho = []
    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        dicho.append(Or(all_in, all_out))
        is_cls[y] = all_in
    nontriv = Or(*[Not(is_cls[y]) for y in CORE])
    tau = Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
              for tv in CORE])
    return And(And(*dicho), nontriv, tau)


def pred_D_struct(T, N):
    """D minus the A12 clause: dichotomy on core + ∃ full classifier τ."""
    CORE = list(range(2, N))
    dicho = []
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        dicho.append(Or(all_in, all_out))
    tau = Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
              for tv in CORE])
    return And(And(*dicho), tau)


def pred_H(T, N):
    CORE = list(range(2, N))
    clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_H_eq(T, N):
    """H minus the b_closed clause: ∃ distinct a,b,c with equation and a-nontriv."""
    CORE = list(range(2, N))
    clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        clauses.append(And(And(*eqs), Or(*diffs)))
    return Or(*clauses) if clauses else BoolVal(False)


def check(N, extras, label):
    s = make_solver()
    T = make_T(N)
    add_E2PM(s, T, N)
    for c in extras(T, N):
        s.add(c)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == sat:
        tag = "sat"
    elif r == unsat:
        tag = "unsat"
    else:
        tag = "unknown"
    if tag == "sat":
        m = s.model()
        witness = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
    else:
        witness = None
    print(f"  [{dt:6.2f}s]  N={N}  {label:40s}: {tag}")
    return tag, witness


def main():
    print("=" * 72)
    print("Factorization of D and H through A12 (core-preserving row)")
    print("=" * 72)

    findings = {}

    for N in N_VALUES:
        print(f"\n--- N={N} ---")

        # D ⇔ D_struct ∧ A12
        # (fwd) D ∧ ¬(D_struct ∧ A12)  -- UNSAT ⇒ D ⊆ D_struct ∧ A12
        t1, w1 = check(N, lambda T, N: [pred_D(T, N), Not(And(pred_D_struct(T, N), pred_A12(T, N)))],
                       "D ∧ ¬(D_struct ∧ A12)")
        # (bwd) (D_struct ∧ A12) ∧ ¬D   -- UNSAT ⇒ D_struct ∧ A12 ⊆ D
        t2, w2 = check(N, lambda T, N: [pred_D_struct(T, N), pred_A12(T, N), Not(pred_D(T, N))],
                       "(D_struct ∧ A12) ∧ ¬D")
        findings[(N, "D")] = (t1, t2, w1, w2)

        # H ⇔ H_eq ∧ A12
        t3, w3 = check(N, lambda T, N: [pred_H(T, N), Not(And(pred_H_eq(T, N), pred_A12(T, N)))],
                       "H ∧ ¬(H_eq ∧ A12)")
        t4, w4 = check(N, lambda T, N: [pred_H_eq(T, N), pred_A12(T, N), Not(pred_H(T, N))],
                       "(H_eq ∧ A12) ∧ ¬H")
        findings[(N, "H")] = (t3, t4, w3, w4)

    print()
    print("=" * 72)
    print("Summary")
    print("=" * 72)
    for (N, prop), (fwd, bwd, _, _) in sorted(findings.items()):
        verdict = "equivalent" if fwd == "unsat" and bwd == "unsat" else \
                  "only ⇒ holds" if fwd == "unsat" else \
                  "only ⇐ holds" if bwd == "unsat" else \
                  "independent"
        print(f"  N={N}  {prop} ⇔ {prop}_struct ∧ A12: fwd={fwd}, bwd={bwd}  ->  {verdict}")

    # Print H counterexample if any
    for (N, prop), (fwd, bwd, wfwd, wbwd) in sorted(findings.items()):
        if prop == "H" and bwd == "sat":
            print(f"\n  Counterexample (N={N}, H_eq ∧ A12 but not H):")
            for row in wbwd:
                print(f"    {row}")


if __name__ == "__main__":
    main()

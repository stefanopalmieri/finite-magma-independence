"""
Canonicality probe: test 13 candidate axioms A_1..A_13 against R, D, H on
extensional 2-pointed magmas (E2PM) at N=5 and N=6.

For each axiom A_k and each N in {5, 6}, run 8 Z3 queries:
  Q1. E2PM + A_k          — is A_k satisfiable alongside E2PM?
  Q2. E2PM + ~A_k         — is A_k NOT forced by E2PM alone?
  Q3. E2PM + A_k + ~R     — does A_k imply R?  (UNSAT means yes)
  Q4. E2PM + A_k + ~D     — does A_k imply D?
  Q5. E2PM + A_k + ~H     — does A_k imply H?
  Q6. E2PM + R + ~A_k     — does R imply A_k?
  Q7. E2PM + D + ~A_k
  Q8. E2PM + H + ~A_k

Per-query timeout: 60 seconds. Results written to probe_results.json.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import (
    And, BoolVal, Distinct, Int, Not, Or, Solver, sat, unknown, unsat,
)


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TIMEOUT_MS = 60_000
N_VALUES = [5, 6]


# ---------------------------------------------------------------------------
# E2PM base encoding (mirrors scripts/enumerate_rdh_iso.py).
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# The three core axioms R, D, H, expressed as pure predicates over T.
# ---------------------------------------------------------------------------

def pred_R(T, N):
    """Retraction pair: exists s, r in core with r(0)=0 and r(s(x))=s(r(x))=x on core."""
    CORE = list(range(2, N))
    if not CORE:
        return BoolVal(False)
    clauses = []
    for s_ in CORE:
        for r_ in CORE:
            conds = [T[r_][0] == 0]
            for x in CORE:
                rs = Or(*[And(T[s_][x] == iv, T[r_][iv] == x) for iv in range(N)])
                sr = Or(*[And(T[r_][x] == iv, T[s_][iv] == x) for iv in range(N)])
                conds.append(And(rs, sr))
            clauses.append(And(*conds))
    return Or(*clauses)


def pred_D(T, N):
    """Classifier dichotomy: every core row is all-in {0,1} or all-out on core;
    at least one non-classifier; at least one full classifier tau (row in {0,1})."""
    CORE = list(range(2, N))
    if not CORE:
        return BoolVal(False)
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


def pred_H(T, N):
    """ICP: exists distinct a,b,c in core, b core-preserving, a(x)=c(b(x)) on core,
    |image(a) on core| >= 2."""
    CORE = list(range(2, N))
    if len(CORE) < 3:
        return BoolVal(False)
    clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    return Or(*clauses)


# ---------------------------------------------------------------------------
# Candidate axioms A_1 .. A_13.
# ---------------------------------------------------------------------------

def pred_A1_surj_subaction(T, N):
    """exists y in core with L_y = T[y][.] surjective on Fin(N)."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        hits = [Or(*[T[y][x] == v for x in range(N)]) for v in range(N)]
        clauses.append(And(*hits))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A2_idempotent(T, N):
    """exists y in core with y*y = y."""
    CORE = list(range(2, N))
    return Or(*[T[y][y] == y for y in CORE]) if CORE else BoolVal(False)


def pred_A3_three_valued_cls(T, N):
    """exists y in core and m in core with row(y)|core in {0,1,m} and all three attained."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        for m in CORE:
            in_set = And(*[Or(T[y][x] == 0, T[y][x] == 1, T[y][x] == m)
                           for x in CORE])
            hits0 = Or(*[T[y][x] == 0 for x in CORE])
            hits1 = Or(*[T[y][x] == 1 for x in CORE])
            hitsm = Or(*[T[y][x] == m for x in CORE])
            clauses.append(And(in_set, hits0, hits1, hitsm))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A4_one_sided_retraction(T, N):
    """exists s, r in core with r(s(x)) = x for all x in core (no sr side)."""
    CORE = list(range(2, N))
    clauses = []
    for s_ in CORE:
        for r_ in CORE:
            conds = []
            for x in CORE:
                conds.append(Or(*[And(T[s_][x] == iv, T[r_][iv] == x)
                                  for iv in range(N)]))
            clauses.append(And(*conds) if conds else BoolVal(True))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A5_self_involution(T, N):
    """exists y in core with y(y(x)) = x for all x in core."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        conds = []
        for x in CORE:
            conds.append(Or(*[And(T[y][x] == iv, T[y][iv] == x)
                              for iv in range(N)]))
        clauses.append(And(*conds) if conds else BoolVal(True))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A6_commutative_pair(T, N):
    """exists y1 != y2 in core with y1*y2 = y2*y1."""
    CORE = list(range(2, N))
    pairs = list(itertools.combinations(CORE, 2))
    return Or(*[T[y1][y2] == T[y2][y1] for y1, y2 in pairs]) if pairs else BoolVal(False)


def pred_A7_associative_element(T, N):
    """exists y in core with (y*y)*y = y*(y*y)."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        cases = [And(T[y][y] == iv, T[iv][y] == T[y][iv]) for iv in range(N)]
        clauses.append(Or(*cases))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A8_core_fixed_point(T, N):
    """exists y in core and x in core with y*x = x."""
    CORE = list(range(2, N))
    atoms = [T[y][x] == x for y in CORE for x in CORE]
    return Or(*atoms) if atoms else BoolVal(False)


def pred_A9_boolean_factor(T, N):
    """exists y in core with row(y)|core taking exactly values {0, 1} (both attained)."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        in_bool = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        hits0 = Or(*[T[y][x] == 0 for x in CORE])
        hits1 = Or(*[T[y][x] == 1 for x in CORE])
        clauses.append(And(in_bool, hits0, hits1))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A10_double_composition(T, N):
    """exists distinct a,b,c in core, b core-preserving, a(x) = c(c(b(x))) on core,
    |image(a) on core| >= 2."""
    CORE = list(range(2, N))
    if len(CORE) < 3:
        return BoolVal(False)
    clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = []
            for iv in range(N):
                for jv in range(N):
                    cases.append(And(T[b][x] == iv,
                                     T[c][iv] == jv,
                                     T[a][x] == T[c][jv]))
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    return Or(*clauses)


def pred_A11_left_cancel_core(T, N):
    """exists y in core with T[y][.] injective on core."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        conds = [T[y][a] != T[y][b] for a, b in itertools.combinations(CORE, 2)]
        clauses.append(And(*conds) if conds else BoolVal(True))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A12_core_preserving(T, N):
    """exists y in core with T[y][core] subset core."""
    CORE = list(range(2, N))
    clauses = []
    for y in CORE:
        conds = [Or(*[T[y][x] == cc for cc in CORE]) for x in CORE]
        clauses.append(And(*conds) if conds else BoolVal(True))
    return Or(*clauses) if clauses else BoolVal(False)


def pred_A13_commutator_trivial(T, N):
    """exists a != b in core with T[T[a][b]][c] = T[T[b][a]][c] for all c in core."""
    CORE = list(range(2, N))
    clauses = []
    for a, b in itertools.permutations(CORE, 2):
        cases = []
        for iv in range(N):
            for jv in range(N):
                same_on_c = And(*[T[iv][c] == T[jv][c] for c in CORE])
                cases.append(And(T[a][b] == iv, T[b][a] == jv, same_on_c))
        clauses.append(Or(*cases))
    return Or(*clauses) if clauses else BoolVal(False)


AXIOMS = [
    ("A1_surj_subaction", pred_A1_surj_subaction,
     "exists y in core, L_y surjective on Fin(N)"),
    ("A2_idempotent", pred_A2_idempotent,
     "exists y in core, y*y = y"),
    ("A3_three_valued_cls", pred_A3_three_valued_cls,
     "exists y,m in core, row(y)|core = {0,1,m} (all attained)"),
    ("A4_one_sided_retraction", pred_A4_one_sided_retraction,
     "exists s,r in core, r(s(x))=x on core"),
    ("A5_self_involution", pred_A5_self_involution,
     "exists y in core, y(y(x))=x on core"),
    ("A6_commutative_pair", pred_A6_commutative_pair,
     "exists y1!=y2 in core, y1*y2 = y2*y1"),
    ("A7_associative_element", pred_A7_associative_element,
     "exists y in core, (y*y)*y = y*(y*y)"),
    ("A8_core_fixed_point", pred_A8_core_fixed_point,
     "exists y,x in core, y*x = x"),
    ("A9_boolean_factor", pred_A9_boolean_factor,
     "exists y in core, row(y)|core = {0,1} (both attained)"),
    ("A10_double_composition", pred_A10_double_composition,
     "exists a,b,c in core distinct, b core-preserving, a(x)=c(c(b(x))), a nontriv"),
    ("A11_left_cancel_core", pred_A11_left_cancel_core,
     "exists y in core, T[y][.] injective on core"),
    ("A12_core_preserving", pred_A12_core_preserving,
     "exists y in core, T[y][core] subset core"),
    ("A13_commutator_trivial", pred_A13_commutator_trivial,
     "exists a!=b in core, T[T[a][b]][c] = T[T[b][a]][c] for all c in core"),
]


# ---------------------------------------------------------------------------
# Query harness.
# ---------------------------------------------------------------------------

QUERY_SPECS = [
    # (query_id, description, builder)
    # builder takes (T, N, axiom_fn) and returns a list of extra clauses to add
    # on top of E2PM.
    ("sat_on_e2pm",        "E2PM & A_k",          lambda T, N, A: [A(T, N)]),
    ("e2pm_sat_notA",      "E2PM & ~A_k",         lambda T, N, A: [Not(A(T, N))]),
    ("A_implies_R_check",  "E2PM & A_k & ~R",     lambda T, N, A: [A(T, N), Not(pred_R(T, N))]),
    ("A_implies_D_check",  "E2PM & A_k & ~D",     lambda T, N, A: [A(T, N), Not(pred_D(T, N))]),
    ("A_implies_H_check",  "E2PM & A_k & ~H",     lambda T, N, A: [A(T, N), Not(pred_H(T, N))]),
    ("R_implies_A_check",  "E2PM & R & ~A_k",     lambda T, N, A: [pred_R(T, N), Not(A(T, N))]),
    ("D_implies_A_check",  "E2PM & D & ~A_k",     lambda T, N, A: [pred_D(T, N), Not(A(T, N))]),
    ("H_implies_A_check",  "E2PM & H & ~A_k",     lambda T, N, A: [pred_H(T, N), Not(A(T, N))]),
]


def run_query(N, clause_builder, axiom_fn):
    s = make_solver()
    T = make_T(N)
    add_E2PM(s, T, N)
    for c in clause_builder(T, N, axiom_fn):
        s.add(c)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        return "sat", dt, table
    if r == unsat:
        return "unsat", dt, None
    return "unknown", dt, None


def sanity_check():
    """Confirm base solver is correct: E2PM + R + D + H should be sat at N=5."""
    for N in N_VALUES:
        s = make_solver()
        T = make_T(N)
        add_E2PM(s, T, N)
        s.add(pred_R(T, N))
        s.add(pred_D(T, N))
        s.add(pred_H(T, N))
        t0 = time.time()
        r = s.check()
        dt = time.time() - t0
        print(f"  Sanity: E2PM + R + D + H at N={N}: {r} ({dt:.2f}s)")
        if r != sat:
            raise SystemExit(f"Sanity check failed at N={N}: expected sat, got {r}")


def main():
    print("=" * 70)
    print("Canonicality probe")
    print("=" * 70)
    print("Sanity checks:")
    sanity_check()

    all_entries = []
    total_start = time.time()

    for axiom_id, axiom_fn, desc in AXIOMS:
        for N in N_VALUES:
            print()
            print(f"--- {axiom_id} @ N={N} ---")
            entry = {
                "axiom_id": axiom_id,
                "description": desc,
                "N": N,
                "queries": {},
            }
            for qid, qdesc, builder in QUERY_SPECS:
                result, dt, witness = run_query(N, builder, axiom_fn)
                q_entry = {"description": qdesc, "result": result, "time_seconds": dt}
                if witness is not None:
                    q_entry["witness"] = witness
                entry["queries"][qid] = q_entry
                flag = "!" if result == "unknown" else " "
                print(f"  [{dt:6.2f}s]{flag} {qid:22s}: {result}")
            all_entries.append(entry)

    elapsed = time.time() - total_start
    print()
    print("=" * 70)
    print(f"Total runtime: {elapsed:.1f}s over {len(AXIOMS) * len(N_VALUES) * len(QUERY_SPECS)} queries")

    out_path = os.path.join(SCRIPT_DIR, "probe_results.json")
    with open(out_path, "w") as f:
        json.dump({
            "timeout_ms": TIMEOUT_MS,
            "N_values": N_VALUES,
            "axioms": [{"id": aid, "description": desc} for aid, _, desc in AXIOMS],
            "entries": all_entries,
            "runtime_seconds": elapsed,
        }, f, indent=2)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()

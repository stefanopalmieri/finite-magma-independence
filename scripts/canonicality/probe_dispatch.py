"""
Internal dispatch (W): axiomatization and independence probe vs S/D/C.

The capability, in ICP's style (existential elements, universal core
equations, guard conditions proven necessary by degeneracy):

  W: exist delta, h1, h2, gamma in core, with (delta, h1, h2) pairwise
     distinct, such that
     (1) TEST     gamma.x in {z1, z2} for all core x   (core-only test:
                  deliberately weaker than D's full classifier, which
                  must be absorber-valued on ALL of S);
     (2) ROUTING  on core: gamma.x = z1 -> delta.x = h1.x
                           gamma.x = z2 -> delta.x = h2.x;
     (3) NON-DEG  each branch realized where the handlers disagree:
                  exists x1 in core: gamma.x1 = z1 and h1.x1 != h2.x1,
                  exists x2 in core: gamma.x2 = z2 and h1.x2 != h2.x2.

Clause (3) forces delta's core row to differ from both handlers' core
rows (at x2 it takes h2's value, which differs from h1's; at x1 vice
versa): delta is a genuinely composite generic function, glued from two
methods along an internal behavioral test -- the algebraic shadow of
single dispatch on a binary type test. Degeneracies blocked: a constant
test (one branch never taken) or handlers agreeing on the taken points
would let every FRM glue trivially.

Structural minimum: three pairwise distinct core elements => N >= 5,
the same bound as C (confirmed UNSAT at N = 4 below).

Queries per N in {5, 6} (per-query timeout 60 s), mirroring
probe_axioms.py:
  Q1. E2PM + W            satisfiable?
  Q2. E2PM + ~W           not forced?
  Q3. E2PM + W + ~S       does W imply S?   (UNSAT = yes)
  Q4. E2PM + W + ~D       does W imply D?
  Q5. E2PM + W + ~C       does W imply C?
  Q6. E2PM + S + ~W       does S imply W?
  Q7. E2PM + D + ~W       does D imply W?
  Q8. E2PM + C + ~W       does C imply W?
  Q9. E2PM + S+D+C + W    joint coexistence?
  Q10. E2PM + S+D+C + ~W  is W free even inside the coexistence world?

Every SAT witness is re-verified by an independent pure-Python checker
before freezing (Z3 finds, independent code confirms — the project's
standard discipline). Also checked concretely: does the canonical N=8
artifact satisfy W? (Relevant to `FactorizationData`'s "branching is
not a table capability": `ite` was placed driver-side.)

Results frozen to probe_dispatch_results.json.
"""

from __future__ import annotations

import itertools
import json
import os

from z3 import (
    And, BoolVal, Distinct, Int, Not, Or, Solver, sat, unknown, unsat,
)

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TIMEOUT_MS = 60_000


# --------------------------------------------------------------- base
# E2PM encoding and S/D/C predicates: verbatim probe_axioms.py
# (R = S, H = C in that file's naming).

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


def pred_S(T, N):
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


def pred_C(T, N):
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
        nontrivial = Or(*[T[a][x] != T[a][y]
                          for x in CORE for y in CORE if x < y])
        clauses.append(And(b_closed, And(*eqs), nontrivial))
    return Or(*clauses)


# --------------------------------------------------------------- W

def pred_W(T, N):
    """Internal dispatch: see module docstring."""
    CORE = list(range(2, N))
    if len(CORE) < 3:
        return BoolVal(False)
    clauses = []
    for d, h1, h2 in itertools.permutations(CORE, 3):
        for g in CORE:
            test = And(*[Or(T[g][x] == 0, T[g][x] == 1) for x in CORE])
            route = And(*[And(
                Or(T[g][x] != 0, T[d][x] == T[h1][x]),
                Or(T[g][x] != 1, T[d][x] == T[h2][x]),
            ) for x in CORE])
            live1 = Or(*[And(T[g][x] == 0, T[h1][x] != T[h2][x])
                         for x in CORE])
            live2 = Or(*[And(T[g][x] == 1, T[h1][x] != T[h2][x])
                         for x in CORE])
            clauses.append(And(test, route, live1, live2))
    return Or(*clauses)


def check_W_concrete(T, N):
    """Independent pure-Python checker (no Z3): exhaustive witness search.
    Returns a witness dict or None."""
    CORE = list(range(2, N))
    for d, h1, h2 in itertools.permutations(CORE, 3):
        for g in CORE:
            if not all(T[g][x] in (0, 1) for x in CORE):
                continue
            ok = all(
                (T[g][x] != 0 or T[d][x] == T[h1][x]) and
                (T[g][x] != 1 or T[d][x] == T[h2][x])
                for x in CORE)
            if not ok:
                continue
            l1 = any(T[g][x] == 0 and T[h1][x] != T[h2][x] for x in CORE)
            l2 = any(T[g][x] == 1 and T[h1][x] != T[h2][x] for x in CORE)
            if l1 and l2:
                return {"delta": d, "h1": h1, "h2": h2, "gamma": g}
    return None


def check_E2PM_concrete(T, N):
    if any(T[0][x] != 0 for x in range(N)):
        return False
    if any(T[1][x] != 1 for x in range(N)):
        return False
    for y in range(2, N):
        if all(T[y][x] == y for x in range(N)):
            return False
    rows = {tuple(T[y]) for y in range(N)}
    return len(rows) == N


# --------------------------------------------------------------- probe

def extract(model, T, N):
    return [[model.evaluate(T[a][b]).as_long() for b in range(N)]
            for a in range(N)]


def query(name, N, want_w, extra):
    """Run one query; returns (status, table or None)."""
    s = make_solver()
    T = make_T(N)
    add_E2PM(s, T, N)
    w = pred_W(T, N)
    s.add(w if want_w else Not(w))
    for e in extra:
        s.add(e(T, N) if not isinstance(e, tuple)
              else Not(e[0](T, N)))
    res = s.check()
    if res == sat:
        return "sat", extract(s.model(), T, N)
    if res == unsat:
        return "unsat", None
    return "unknown", None


def main():
    results = {}
    witnesses = {}

    # Structural minimum: W impossible at N = 4.
    st, _ = query("W@4", 4, True, [])
    results["N4: E2PM+W"] = st
    print(f"N=4  E2PM+W                  {st}   (expect unsat: 3 distinct "
          "core elements needed)")

    for N in (5, 6):
        qs = [
            ("E2PM+W", True, []),
            ("E2PM+~W", False, []),
            ("W+~S (W=>S?)", True, [("neg", pred_S)]),
            ("W+~D (W=>D?)", True, [("neg", pred_D)]),
            ("W+~C (W=>C?)", True, [("neg", pred_C)]),
            ("S+~W (S=>W?)", False, [pred_S]),
            ("D+~W (D=>W?)", False, [pred_D]),
            ("C+~W (C=>W?)", False, [pred_C]),
            ("S+D+C+W", True, [pred_S, pred_D, pred_C]),
            ("S+D+C+~W", False, [pred_S, pred_D, pred_C]),
        ]
        for name, want_w, extra in qs:
            wrapped = [((lambda f: (lambda T, n: Not(f(T, n))))(e[1])
                        if isinstance(e, tuple) else e) for e in extra]
            st, tbl = query(name, N, want_w, wrapped)
            key = f"N{N}: {name}"
            results[key] = st
            line = f"N={N}  {name:<18} {st}"
            if st == "sat" and tbl is not None:
                assert check_E2PM_concrete(tbl, N), "E2PM re-check failed"
                wit = check_W_concrete(tbl, N)
                if want_w:
                    assert wit is not None, "W re-check failed"
                    line += f"   verified {wit}"
                else:
                    assert wit is None, "~W re-check failed"
                    line += "   verified (no W witness)"
                witnesses[key] = {"table": tbl, "W_witness": wit}
            print(line)

    # The canonical N=8 artifact: does the frozen table have W?
    dotA8 = [
        [0, 0, 0, 0, 0, 0, 0, 0],
        [1, 1, 1, 1, 1, 1, 1, 1],
        [0, 0, 5, 6, 7, 2, 3, 4],
        [0, 1, 5, 6, 7, 2, 3, 4],
        [0, 0, 5, 7, 6, 2, 4, 3],
        [0, 0, 1, 1, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 1, 1],
        [0, 0, 0, 0, 1, 0, 0, 1],
    ]
    wit = check_W_concrete(dotA8, 8)
    results["artifactN8: W"] = "sat" if wit else "no witness"
    witnesses["artifactN8"] = {"W_witness": wit}
    print(f"\ncanonical N=8 artifact: W witness = {wit}")

    out = os.path.join(SCRIPT_DIR, "probe_dispatch_results.json")
    with open(out, "w") as f:
        json.dump({"results": results, "witnesses": witnesses}, f, indent=1)
    print(f"\nfrozen: {out}")


if __name__ == "__main__":
    main()

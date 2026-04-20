#!/usr/bin/env python3
"""
Deep exhaustive search for finite extensional 2-pointed magma (E2PM)
satisfying F+D+H AND strict self-simulation simultaneously.

Search matrix (N = 6..10, 600s timeout per query):
  1. R+F+selfsim            (no D, no H requirement)
  2. R+F+D+H+selfsim        (all five)
  3. R+F+selfsim+NOT_D+NOT_H (self-sim without D and H)

Key: if (1) SAT but (3) UNSAT, then D/H are necessary for self-sim.
"""

from z3 import *
import time
import sys

TIMEOUT_MS = 600_000  # 10 minutes per query


def build_solver(N, require_D=False, require_H=False, forbid_D=False, forbid_H=False):
    """
    Build Z3 solver for E2PM with R+F+strict-self-sim,
    optionally requiring or forbidding D and H.
    """
    core = list(range(2, N))

    dot = [[Int(f"d_{y}_{x}") for x in range(N)] for y in range(N)]
    s_var = Int("s")
    r_var = Int("r")
    t_var = Int("t")

    solver = Solver()
    solver.set("timeout", TIMEOUT_MS)

    # --- Domain constraints ---
    for y in range(N):
        for x in range(N):
            solver.add(dot[y][x] >= 0, dot[y][x] < N)
    solver.add(s_var >= 2, s_var < N)
    solver.add(r_var >= 2, r_var < N)
    solver.add(t_var >= 0, t_var < N)

    # --- Absorbers: row 0 all 0s, row 1 all 1s ---
    for x in range(N):
        solver.add(dot[0][x] == 0)
        solver.add(dot[1][x] == 1)

    # --- No extra absorbers ---
    for y in core:
        solver.add(Not(And([dot[y][x] == y for x in range(N)])))

    # --- Extensionality: all rows pairwise distinct ---
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            solver.add(Or([dot[y1][x] != dot[y2][x] for x in range(N)]))

    # --- Symbolic dot lookup via If-chain ---
    def dlookup(a_expr, b_expr):
        """Look up dot[a_expr][b_expr] where a_expr, b_expr are Z3 expressions."""
        result = dot[0][0]  # default (will be overridden)
        for y in range(N):
            for x in range(N):
                result = If(And(a_expr == y, b_expr == x), dot[y][x], result)
        return result

    # --- Retraction pair: mutual inverse on core + anchor ---
    for x in core:
        solver.add(dlookup(r_var, dlookup(s_var, IntVal(x))) == x)
        solver.add(dlookup(s_var, dlookup(r_var, IntVal(x))) == x)
    solver.add(dlookup(r_var, IntVal(0)) == 0)  # anchor: r(0) = 0

    # --- F: rep values, all distinct ---
    # rep[k] = s^k(0) computed symbolically
    rep = [IntVal(0)]  # rep(0) = 0
    for k in range(1, N):
        rep.append(dlookup(s_var, rep[k - 1]))

    # Pairwise distinct rep values
    for i in range(N):
        for j in range(i + 1, N):
            solver.add(rep[i] != rep[j])

    # --- Strict self-simulation ---
    # dot(dot(t, rep(a)), rep(b)) = dot(a, b) for ALL a, b
    # This requires double symbolic indexing through rep values.
    for a in range(N):
        for b in range(N):
            inner = dlookup(t_var, rep[a])       # dot[t][rep[a]]
            outer = dlookup(inner, rep[b])        # dot[dot[t][rep[a]]][rep[b]]
            solver.add(outer == dot[a][b])

    # --- D: Classifier Dichotomy ---
    if require_D:
        cls_var = Int("cls")
        solver.add(cls_var >= 2, cls_var < N)
        # Classifier outputs only 0 or 1 on all inputs
        for x in range(N):
            solver.add(Or(dlookup(cls_var, IntVal(x)) == 0,
                          dlookup(cls_var, IntVal(x)) == 1))
        # Global dichotomy: every core element is either all-absorber or all-core on core
        for y in core:
            all_abs = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
            all_core = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
            solver.add(Or(all_abs, all_core))
        # Non-degeneracy: at least one core element maps core to core
        solver.add(Or([And(dot[y][x] != 0, dot[y][x] != 1) for y in core for x in core]))

    if forbid_D:
        # NOT D: negate at least one part of dichotomy.
        # The simplest negation: there exists a core element that is NEITHER
        # all-absorber NOR all-core on core (i.e., it's mixed).
        # OR no classifier exists. OR degeneracy.
        # We use: exists core element with mixed output on core.
        # This is the strongest useful negation.
        mixed_clauses = []
        for y in core:
            all_abs = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
            all_core = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
            mixed_clauses.append(And(Not(all_abs), Not(all_core)))
        solver.add(Or(mixed_clauses))

    # --- H: ICP (Internal Composition Property) ---
    if require_H:
        a_icp = Int("a_icp")
        b_icp = Int("b_icp")
        c_icp = Int("c_icp")
        solver.add(a_icp >= 2, a_icp < N)
        solver.add(b_icp >= 2, b_icp < N)
        solver.add(c_icp >= 2, c_icp < N)
        solver.add(a_icp != b_icp, a_icp != c_icp, b_icp != c_icp)
        # b is core-preserving
        for x in core:
            solver.add(And(dlookup(b_icp, IntVal(x)) != 0,
                           dlookup(b_icp, IntVal(x)) != 1))
        # a(x) = c(b(x)) on core
        for x in core:
            solver.add(dlookup(a_icp, IntVal(x)) == dlookup(c_icp, dlookup(b_icp, IntVal(x))))
        # a is non-trivial on core
        solver.add(Or([dlookup(a_icp, IntVal(x)) != dlookup(a_icp, IntVal(y))
                        for x in core for y in core if x < y]))

    if forbid_H:
        # NOT H: for ALL triples of pairwise distinct non-absorbers (a,b,c),
        # if b is core-preserving, then either a(x) != c(b(x)) for some x in core,
        # or a is trivial (constant) on core.
        # This is a universal statement over all triples -- hard for SAT.
        # We enumerate all possible triple assignments.
        for a_val in core:
            for b_val in core:
                for c_val in core:
                    if a_val == b_val or a_val == c_val or b_val == c_val:
                        continue
                    # If b is core-preserving AND a(x) = c(b(x)) on all core AND a non-trivial
                    # => contradiction. So negate: at least one fails.
                    b_core_pres = And([And(dot[b_val][x] != 0, dot[b_val][x] != 1) for x in core])
                    comp_clauses = []
                    for x in core:
                        bx = dot[b_val][x]  # Z3 var
                        # c(bx) requires symbolic lookup since bx is a variable
                        c_of_bx = dlookup(IntVal(c_val), bx)
                        comp_clauses.append(dot[a_val][x] == c_of_bx)
                    composition = And(comp_clauses)

                    nontrivial = Or([dot[a_val][x] != dot[a_val][y]
                                     for x in core for y in core if x < y])

                    # Negate the conjunction: at least one must fail
                    solver.add(Not(And(b_core_pres, composition, nontrivial)))

    return solver, dot, s_var, r_var, t_var, rep, core


def run_search(N, require_D=False, require_H=False, forbid_D=False, forbid_H=False):
    """Run one search configuration and return results."""
    label_parts = ["R", "F", "selfsim"]
    if require_D:
        label_parts.append("D")
    if require_H:
        label_parts.append("H")
    if forbid_D:
        label_parts.append("NOT_D")
    if forbid_H:
        label_parts.append("NOT_H")
    label = "+".join(label_parts)

    print(f"\n--- N={N}, {label} ---")
    sys.stdout.flush()

    t0 = time.time()
    solver, dot, s_var, r_var, t_var, rep, core = build_solver(
        N, require_D=require_D, require_H=require_H,
        forbid_D=forbid_D, forbid_H=forbid_H
    )
    build_time = time.time() - t0
    print(f"  Solver built in {build_time:.1f}s")
    sys.stdout.flush()

    t0 = time.time()
    result = solver.check()
    solve_time = time.time() - t0
    print(f"  Result: {result} ({solve_time:.1f}s)")
    sys.stdout.flush()

    if result == sat:
        m = solver.model()
        s_val = m.evaluate(s_var).as_long()
        r_val = m.evaluate(r_var).as_long()
        t_val = m.evaluate(t_var).as_long()

        table = []
        for y in range(N):
            row = [m.evaluate(dot[y][x]).as_long() for x in range(N)]
            table.append(row)

        # Compute concrete rep values
        rep_vals = [0]
        for k in range(1, N):
            rep_vals.append(table[s_val][rep_vals[k - 1]])

        print(f"  s={s_val}, r={r_val}, t={t_val}")
        print(f"  rep = {rep_vals}")
        print(f"  Table:")
        for y in range(N):
            print(f"    {y}: {table[y]}")

        # Verify strict self-sim
        ok = True
        for a in range(N):
            for b in range(N):
                lhs = table[table[t_val][rep_vals[a]]][rep_vals[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    print(f"  FAIL: dot(dot({t_val}, rep({a})), rep({b})) = {lhs} != {rhs}")
                    ok = False
        if ok:
            print(f"  Strict self-simulation VERIFIED for all {N*N} cells")

        # Verify F (rep injectivity)
        if len(set(rep_vals)) == N:
            print(f"  F (faithful encoding) VERIFIED: all {N} rep values distinct")
        else:
            print(f"  F FAIL: rep values not all distinct!")

        # Check D (dichotomy)
        has_classifier = False
        has_mixed = False
        has_core_to_core = False
        for y in core:
            core_out = [table[y][x] for x in core]
            is_abs = all(v in (0, 1) for v in core_out)
            is_core = all(v not in (0, 1) for v in core_out)
            if not is_abs and not is_core:
                has_mixed = True
            if is_core:
                has_core_to_core = True
            # Check if classifier
            all_out = [table[y][x] for x in range(N)]
            if all(v in (0, 1) for v in all_out):
                has_classifier = True
            role = "classifier" if is_abs and all(v in (0,1) for v in all_out) else \
                   ("core-preserving" if is_core else "mixed")
            print(f"  Element {y}: {role} (core outputs: {core_out})")

        d_holds = has_classifier and not has_mixed and has_core_to_core
        print(f"  D (classifier dichotomy): {'HOLDS' if d_holds else 'FAILS'}")

        # Check H (ICP)
        h_holds = False
        for a_v in core:
            for b_v in core:
                for c_v in core:
                    if a_v == b_v or a_v == c_v or b_v == c_v:
                        continue
                    # b core-preserving?
                    if any(table[b_v][x] in (0, 1) for x in core):
                        continue
                    # a(x) = c(b(x)) on core?
                    comp_ok = all(table[a_v][x] == table[c_v][table[b_v][x]] for x in core)
                    if not comp_ok:
                        continue
                    # a non-trivial?
                    a_core_out = [table[a_v][x] for x in core]
                    if len(set(a_core_out)) > 1:
                        h_holds = True
                        print(f"  H (ICP): HOLDS via a={a_v}, b={b_v}, c={c_v}")
                        break
                if h_holds:
                    break
            if h_holds:
                break
        if not h_holds:
            print(f"  H (ICP): FAILS")

        # Info about t
        t_core_out = [table[t_val][x] for x in core]
        t_is_cls = all(v in (0, 1) for v in t_core_out)
        print(f"  Sim term t={t_val}: {'classifier' if t_is_cls else 'non-classifier'}")
        print(f"  t == s? {t_val == s_val}. t == r? {t_val == r_val}")

        return ("SAT", table, s_val, r_val, t_val, rep_vals)

    elif result == unsat:
        return ("UNSAT", None, None, None, None, None)
    else:
        return ("TIMEOUT", None, None, None, None, None)


def main():
    print("=" * 70)
    print("DEEP SELF-SIMULATION SEARCH")
    print("=" * 70)
    print(f"Timeout per query: {TIMEOUT_MS // 1000}s")
    print(f"Search sizes: N = 6..10")
    print()

    results = {}

    configs = [
        ("R+F+selfsim",          dict(require_D=False, require_H=False, forbid_D=False, forbid_H=False)),
        ("R+F+D+H+selfsim",      dict(require_D=True,  require_H=True,  forbid_D=False, forbid_H=False)),
        ("R+F+selfsim+NOT_D+NOT_H", dict(require_D=False, require_H=False, forbid_D=True,  forbid_H=True)),
    ]

    for config_name, kwargs in configs:
        print("\n" + "=" * 70)
        print(f"CONFIGURATION: {config_name}")
        print("=" * 70)
        sys.stdout.flush()

        for N in range(6, 11):
            result = run_search(N, **kwargs)
            results[(config_name, N)] = result[0]
            sys.stdout.flush()

            # If SAT, we found what we need for this config
            # But continue to see at what sizes it becomes SAT

    # Summary table
    print("\n\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    header = f"{'Condition':<30} " + " ".join(f"N={n:<4}" for n in range(6, 11))
    print(header)
    print("-" * len(header))
    for config_name, _ in configs:
        row = f"{config_name:<30} "
        for N in range(6, 11):
            r = results.get((config_name, N), "?")
            row += f"{r:<6} "
        print(row)

    print("\n" + "=" * 70)
    print("INTERPRETATION")
    print("=" * 70)

    # Analysis
    rf_sat = any(results.get(("R+F+selfsim", N)) == "SAT" for N in range(6, 11))
    rfdh_sat = any(results.get(("R+F+D+H+selfsim", N)) == "SAT" for N in range(6, 11))
    neg_sat = any(results.get(("R+F+selfsim+NOT_D+NOT_H", N)) == "SAT" for N in range(6, 11))

    if rf_sat and not rfdh_sat:
        print("Self-sim possible WITHOUT D+H, but NOT with them -> D+H obstruct self-sim!")
    elif rf_sat and rfdh_sat:
        print("Self-sim possible both with and without D+H.")
        if neg_sat:
            print("Self-sim also possible with explicit NOT D + NOT H -> D+H independent of self-sim.")
        else:
            print("But self-sim REQUIRES D or H (NOT_D+NOT_H is UNSAT) -> D/H necessary for self-sim!")
    elif not rf_sat:
        rf_unsat_all = all(results.get(("R+F+selfsim", N)) == "UNSAT" for N in range(6, 11))
        if rf_unsat_all:
            print("R+F+strict-self-sim is UNSAT for all tested sizes (6-10).")
            print("Strict self-simulation may be impossible for finite E2PM with faithful encoding.")
        else:
            print("Some queries timed out. Inconclusive.")


if __name__ == "__main__":
    main()

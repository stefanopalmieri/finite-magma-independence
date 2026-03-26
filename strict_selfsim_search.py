#!/usr/bin/env python3
"""
Strict self-simulation search for extensional 2-pointed magmas.

DEFINITIONS:
- rep(k) = s^k(0) computed in the ground algebra
- Strict self-simulation: rep injective AND ∃ t ∀ a,b: dot(dot(t,rep(a)),rep(b)) = dot(a,b)

TASK 2: Check existing counterexamples
TASK 1: SAT search for R+D+H + strict self-simulation
TASK 4: Role analysis of strict witnesses
"""

from z3 import *
import itertools

# ============================================================
# TASK 2: Check existing counterexamples
# ============================================================

def compute_rep(table, s, z1, N):
    """Compute rep(k) = s^k(z1) for k=0..N-1."""
    rep = [0] * N
    rep[0] = z1
    for k in range(1, N):
        rep[k] = table[s][rep[k-1]]
    return rep

def check_strict_selfsim(table, N, s, r, z1, z2, name):
    """Check strict self-simulation for a given table."""
    print(f"\n{'='*60}")
    print(f"Checking: {name}")
    print(f"N={N}, s={s}, r={r}, z1={z1}, z2={z2}")
    print(f"{'='*60}")

    # Print table
    for i in range(N):
        print(f"  {i}: {table[i]}")

    # Compute rep
    rep = compute_rep(table, s, z1, N)
    print(f"\nrep values: {rep}")
    for k in range(N):
        print(f"  rep({k}) = {rep[k]}")

    # Check injectivity
    injective = len(set(rep)) == N
    print(f"\nrep injective: {injective}")
    if not injective:
        # Show collisions
        seen = {}
        for k in range(N):
            if rep[k] in seen:
                print(f"  COLLISION: rep({seen[rep[k]]}) = rep({k}) = {rep[k]}")
            else:
                seen[rep[k]] = k
        print("  => Strict self-simulation IMPOSSIBLE (rep not injective)")
        return None

    # Check all candidate t values
    print(f"\nChecking all t in {{0,...,{N-1}}}:")
    witnesses = []
    for t in range(N):
        ok = True
        failures = []
        for a in range(N):
            for b in range(N):
                lhs = table[table[t][rep[a]]][rep[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    ok = False
                    failures.append((a, b, lhs, rhs))
        if ok:
            print(f"  t={t}: SATISFIES strict self-simulation!")
            witnesses.append(t)
        else:
            print(f"  t={t}: FAILS ({len(failures)} violations, first: "
                  f"dot(dot({t},rep({failures[0][0]})),rep({failures[0][1]}))="
                  f"{failures[0][2]} != dot({failures[0][0]},{failures[0][1]})={failures[0][3]})")

    if witnesses:
        print(f"\n  RESULT: Strict self-simulation holds with t in {witnesses}")
    else:
        print(f"\n  RESULT: NO t works. Strict self-simulation FAILS.")

    return witnesses


print("=" * 70)
print("TASK 2: CHECK EXISTING COUNTEREXAMPLES")
print("=" * 70)

# Table 1: N=8 R-not-D counterexample
table1 = [
    [0,0,0,0,0,0,0,0],
    [1,1,1,1,1,1,1,1],
    [3,3,7,3,4,6,5,2],
    [0,1,7,3,4,6,5,2],
    [0,0,0,0,0,0,1,0],
    [6,2,6,2,1,1,1,1],
    [0,0,5,2,2,2,2,2],
    [2,2,2,1,2,2,6,3],
]
check_strict_selfsim(table1, 8, 2, 3, 0, 1, "Table 1: N=8 R-not-D (Countermodel.lean)")

# Table 2: N=6 R-not-H structural counterexample
table2 = [
    [0,0,0,0,0,0],
    [1,1,1,1,1,1],
    [0,3,3,2,5,4],
    [2,4,5,5,1,4],
    [5,3,0,0,3,2],
    [4,2,2,2,2,2],
]
check_strict_selfsim(table2, 6, 2, 2, 0, 1, "Table 2: N=6 R-not-H (sNoH6)")

# Table 3: N=5 coexistence witness
table3 = [
    [0,0,0,0,0],
    [1,1,1,1,1],
    [0,2,2,3,4],
    [0,0,0,1,0],
    [0,1,0,1,0],
]
check_strict_selfsim(table3, 5, 2, 2, 0, 1, "Table 3: N=5 Witness5.lean")

# Table 4: N=6 coexistence witness
table4 = [
    [0,0,0,0,0,0],
    [1,1,1,1,1,1],
    [3,3,4,2,5,3],
    [0,1,3,5,2,4],
    [0,0,1,0,1,1],
    [2,2,5,4,3,2],
]
check_strict_selfsim(table4, 6, 2, 3, 0, 1, "Table 4: N=6 Witness6.lean")


# ============================================================
# TASK 1: SAT search for R+D+H + strict self-simulation
# ============================================================

print("\n\n" + "=" * 70)
print("TASK 1: SAT SEARCH FOR R+D+H + STRICT SELF-SIMULATION")
print("=" * 70)

def z3_dot(table_vars, N, i, j):
    """Symbolic lookup: table_vars[i][j] using nested If."""
    # i and j are Z3 expressions
    result = table_vars[0][0]
    for r in range(N):
        for c in range(N):
            result = If(And(i == r, j == c), table_vars[r][c], result)
    return result

def z3_dot_concrete_row(table_vars, N, row, j):
    """Symbolic lookup: table_vars[row][j] where row is concrete int."""
    result = table_vars[row][0]
    for c in range(1, N):
        result = If(j == c, table_vars[row][c], result)
    return result

def z3_dot_sym(table_vars, N, i, j):
    """Fully symbolic dot lookup."""
    result = table_vars[0][0]
    for r in range(N):
        for c in range(N):
            result = If(And(i == r, j == c), table_vars[r][c], result)
    return result

def search_strict_selfsim(N):
    print(f"\n{'='*60}")
    print(f"Searching N={N}")
    print(f"{'='*60}")

    solver = Solver()
    solver.set("timeout", 120000)  # 2 min timeout

    # Cayley table variables
    T = [[Int(f"t_{i}_{j}") for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(N):
            solver.add(T[i][j] >= 0, T[i][j] < N)

    # z1=0, z2=1 absorbers
    for j in range(N):
        solver.add(T[0][j] == 0, T[j][0] == 0)
        solver.add(T[1][j] == 1, T[j][1] == 1)

    # No other absorbers: for each k >= 2, row k is not all-k or column k is not all-k
    for k in range(2, N):
        # k is not a left absorber OR not a right absorber
        # Left absorber: T[k][j] == k for all j
        # Right absorber: T[j][k] == k for all j
        # "No absorber" means NOT(left AND right)
        # i.e., ∃ j: T[k][j] ≠ k  OR  ∃ j: T[j][k] ≠ k
        left_abs = And([T[k][j] == k for j in range(N)])
        right_abs = And([T[j][k] == k for j in range(N)])
        solver.add(Not(And(left_abs, right_abs)))

    # Extensionality: all rows distinct
    for i in range(N):
        for j in range(i+1, N):
            solver.add(Or([T[i][k] != T[j][k] for k in range(N)]))

    # s, r variables
    s = Int('s')
    r = Int('r')
    core = list(range(2, N))  # non-absorber indices

    solver.add(s >= 2, s < N)
    solver.add(r >= 2, r < N)

    # HasRetractPair: r·(s·x)=x for core x, s·(r·x)=x for core x, r·0=0
    for x in core:
        # r·(s·x) = x
        sx = z3_dot_sym(T, N, s, IntVal(x))
        rsx = z3_dot_sym(T, N, r, sx)
        solver.add(rsx == x)

        # s·(r·x) = x
        rx = z3_dot_sym(T, N, r, IntVal(x))
        srx = z3_dot_sym(T, N, s, rx)
        solver.add(srx == x)

    # r·0 = 0
    r0 = z3_dot_sym(T, N, r, IntVal(0))
    solver.add(r0 == 0)

    # HasDichotomy: ∃ classifier c_var with global dichotomy
    c_var = Int('c_var')
    solver.add(c_var >= 2, c_var < N)

    # c_var·x ∈ {0, 1} for all x (global dichotomy)
    for x in range(N):
        cx = z3_dot_sym(T, N, c_var, IntVal(x))
        solver.add(Or(cx == 0, cx == 1))

    # Non-degeneracy: c_var hits both 0 and 1
    solver.add(Or([z3_dot_sym(T, N, c_var, IntVal(x)) == 0 for x in range(N)]))
    solver.add(Or([z3_dot_sym(T, N, c_var, IntVal(x)) == 1 for x in range(N)]))

    # HasICP: ∃ a,b,c pairwise distinct non-absorbers,
    # b core-preserving, a·x = c·(b·x) on core, a non-trivial
    ha = Int('ha')
    hb = Int('hb')
    hc = Int('hc')
    solver.add(ha >= 2, ha < N, hb >= 2, hb < N, hc >= 2, hc < N)
    solver.add(Distinct(ha, hb, hc))

    # b core-preserving: b·x ∈ core for core x
    for x in core:
        bx = z3_dot_sym(T, N, hb, IntVal(x))
        solver.add(bx >= 2)  # non-absorber

    # a·x = c·(b·x) on core
    for x in core:
        ax = z3_dot_sym(T, N, ha, IntVal(x))
        bx = z3_dot_sym(T, N, hb, IntVal(x))
        cbx = z3_dot_sym(T, N, hc, bx)
        solver.add(ax == cbx)

    # a non-trivial: ∃ core x where a·x ∉ {0, 1}
    solver.add(Or([And(z3_dot_sym(T, N, ha, IntVal(x)) != 0,
                       z3_dot_sym(T, N, ha, IntVal(x)) != 1) for x in core]))

    # STRICT SELF-SIMULATION
    # rep(k) = s^k(0), computed symbolically
    # We need rep for each k = 0..N-1
    # rep(0) = 0
    # rep(k) = T[s][rep(k-1)]

    # Since s is symbolic, rep values are symbolic too
    rep = [None] * N
    rep[0] = IntVal(0)
    for k in range(1, N):
        rep[k] = z3_dot_sym(T, N, s, rep[k-1])

    # rep injectivity
    for i in range(N):
        for j in range(i+1, N):
            solver.add(rep[i] != rep[j])

    # ∃ t such that dot(dot(t, rep(a)), rep(b)) = dot(a, b) for all a, b
    t_var = Int('t_var')
    solver.add(t_var >= 0, t_var < N)

    for a in range(N):
        for b in range(N):
            # dot(t_var, rep(a))
            t_rep_a = z3_dot_sym(T, N, t_var, rep[a])
            # dot(dot(t_var, rep(a)), rep(b))
            lhs = z3_dot_sym(T, N, t_rep_a, rep[b])
            # dot(a, b)
            rhs = T[a][b]
            solver.add(lhs == rhs)

    print(f"Constraints added. Solving...")
    result = solver.check()
    print(f"Result: {result}")

    if result == sat:
        m = solver.model()
        s_val = m.eval(s).as_long()
        r_val = m.eval(r).as_long()
        t_val = m.eval(t_var).as_long()
        c_val = m.eval(c_var).as_long()
        ha_val = m.eval(ha).as_long()
        hb_val = m.eval(hb).as_long()
        hc_val = m.eval(hc).as_long()

        table = [[m.eval(T[i][j]).as_long() for j in range(N)] for i in range(N)]

        print(f"\nFOUND WITNESS!")
        print(f"s={s_val}, r={r_val}, t={t_val}, classifier={c_val}")
        print(f"ICP: a={ha_val}, b={hb_val}, c={hc_val}")
        print(f"\nCayley table:")
        for i in range(N):
            print(f"  {i}: {table[i]}")

        # Compute and display rep
        rep_vals = compute_rep(table, s_val, 0, N)
        print(f"\nrep values: {rep_vals}")
        for k in range(N):
            print(f"  rep({k}) = {rep_vals[k]}")

        # Verify strict self-sim
        print(f"\nVerification of strict self-sim with t={t_val}:")
        ok = True
        for a in range(N):
            for b in range(N):
                lhs = table[table[t_val][rep_vals[a]]][rep_vals[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    print(f"  FAIL: a={a}, b={b}: {lhs} != {rhs}")
                    ok = False
        if ok:
            print(f"  ALL {N*N} equations verified!")

        # Verify retraction
        print(f"\nVerification of retraction (s={s_val}, r={r_val}):")
        ret_ok = True
        for x in core:
            sx = table[s_val][x]
            rsx = table[r_val][sx]
            if rsx != x:
                print(f"  FAIL: r·(s·{x}) = {rsx} != {x}")
                ret_ok = False
            rx = table[r_val][x]
            srx = table[s_val][rx]
            if srx != x:
                print(f"  FAIL: s·(r·{x}) = {srx} != {x}")
                ret_ok = False
        if table[r_val][0] != 0:
            print(f"  FAIL: r·0 = {table[r_val][0]} != 0")
            ret_ok = False
        if ret_ok:
            print(f"  Retraction pair verified!")

        # Verify dichotomy
        print(f"\nVerification of dichotomy (classifier={c_val}):")
        c_row = table[c_val]
        dic_ok = all(v in (0, 1) for v in c_row)
        hits_0 = 0 in c_row
        hits_1 = 1 in c_row
        print(f"  Row {c_val}: {c_row}")
        print(f"  All values in {{0,1}}: {dic_ok}")
        print(f"  Hits 0: {hits_0}, Hits 1: {hits_1}")

        return table, s_val, r_val, t_val, c_val, ha_val, hb_val, hc_val
    else:
        print(f"No witness found at N={N}.")
        return None

witnesses = {}
for N in [5, 6]:
    result = search_strict_selfsim(N)
    if result is not None:
        witnesses[N] = result


# ============================================================
# TASK 4: Role analysis of strict witnesses
# ============================================================

print("\n\n" + "=" * 70)
print("TASK 4: ROLE ANALYSIS OF STRICT SELF-SIMULATION WITNESSES")
print("=" * 70)

def analyze_roles(table, N, s, r, t, c, ha, hb, hc):
    print(f"\n--- Role Analysis for N={N} witness ---")
    print(f"s={s}, r={r}, t={t}, classifier={c}")
    print(f"ICP triple: a={ha}, b={hb}, c={hc}")

    # Is t the classifier?
    print(f"\nt == classifier? {t == c}")
    print(f"t == s? {t == s}")
    print(f"t == r? {t == r}")
    print(f"t == ha? {t == ha}")
    print(f"t == hb? {t == hb}")
    print(f"t == hc? {t == hc}")

    # Row analysis for t
    t_row = table[t]
    print(f"\nRow t={t}: {t_row}")

    # Is t a classifier (row all in {0,1})?
    is_classifier = all(v in (0, 1) for v in t_row)
    print(f"t is a classifier (row ⊆ {{0,1}}): {is_classifier}")

    # Is t absorbing?
    left_abs = all(table[t][j] == t for j in range(N))
    right_abs = all(table[j][t] == t for j in range(N))
    print(f"t is left-absorbing: {left_abs}")
    print(f"t is right-absorbing: {right_abs}")

    # Is t idempotent?
    print(f"t·t = {table[t][t]} (idempotent: {table[t][t] == t})")

    # Is t core-preserving?
    core = list(range(2, N))
    core_pres = all(table[t][x] >= 2 for x in core)
    print(f"t is core-preserving: {core_pres}")

    # What does t do to each element?
    print(f"\nt's action on all elements:")
    for x in range(N):
        print(f"  t·{x} = {table[t][x]}")

    # Column t
    print(f"\nColumn t={t}: {[table[i][t] for i in range(N)]}")

    # rep values
    rep = compute_rep(table, s, 0, N)
    print(f"\nrep values: {rep}")
    print(f"rep is a permutation of {{0,...,{N-1}}}: {sorted(rep) == list(range(N))}")

    # What does t·rep(k) give?
    print(f"\nt·rep(k) values:")
    for k in range(N):
        print(f"  t·rep({k}) = t·{rep[k]} = {table[t][rep[k]]}")

    # Check if t·rep is injective
    t_rep_vals = [table[t][rep[k]] for k in range(N)]
    print(f"t·rep injective: {len(set(t_rep_vals)) == N}")


# Analyze any witnesses from Task 2 that had strict self-sim
# (We'll call this after Task 2 results are known)

# Also check the Task 2 tables for analysis
print("\n--- Re-checking Task 2 results for role analysis ---")

# Re-run checks and analyze witnesses
for name, table, N, s, r, z1, z2 in [
    ("Table 1: N=8 R-not-D", table1, 8, 2, 3, 0, 1),
    ("Table 2: N=6 R-not-H", table2, 6, 2, 2, 0, 1),
    ("Table 3: N=5 Witness5", table3, 5, 2, 2, 0, 1),
    ("Table 4: N=6 Witness6", table4, 6, 2, 3, 0, 1),
]:
    rep = compute_rep(table, s, z1, N)
    if len(set(rep)) == N:
        # Check all t
        for t in range(N):
            ok = True
            for a in range(N):
                for b in range(N):
                    if table[table[t][rep[a]]][rep[b]] != table[a][b]:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                print(f"\n{name}: has strict self-sim with t={t}")
                # Find classifier
                c = None
                for k in range(2, N):
                    row = table[k]
                    if all(v in (0, 1) for v in row) and 0 in row and 1 in row:
                        c = k
                        break
                analyze_roles(table, N, s, r, t, c, None, None, None)

# Analyze SAT search witnesses
for N, result in witnesses.items():
    if result is not None:
        table, s, r, t, c, ha, hb, hc = result
        analyze_roles(table, N, s, r, t, c, ha, hb, hc)

print("\n\nDone.")

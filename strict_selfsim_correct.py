"""
Strict self-simulation: correct SAT search.

The previous search incorrectly assumed s·0 = 0 (right-absorption).
Left-absorption says T[0][j] = 0 for all j (ROW 0 constant).
s·0 = T[s][0] is column 0 of row s, which is NOT forced to be 0.

We search for E2PM + retraction pair + rep injective + strict self-sim,
with or without D and H.
"""
from z3 import *

def search_strict_selfsim(N, require_D=False, require_H=False):
    core = list(range(2, N))

    dot = [[Int(f"d_{y}_{x}") for x in range(N)] for y in range(N)]
    s_var = Int("s")
    r_var = Int("r")
    t_var = Int("t")

    solver = Solver()

    # Domain
    for y in range(N):
        for x in range(N):
            solver.add(dot[y][x] >= 0, dot[y][x] < N)
    solver.add(s_var >= 2, s_var < N)
    solver.add(r_var >= 2, r_var < N)
    solver.add(t_var >= 0, t_var < N)

    # Absorbers (LEFT absorption only: row 0 all 0s, row 1 all 1s)
    for x in range(N):
        solver.add(dot[0][x] == 0)
        solver.add(dot[1][x] == 1)

    # No other absorbers
    for y in core:
        solver.add(Not(And([dot[y][x] == y for x in range(N)])))

    # Extensionality
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            solver.add(Or([dot[y1][x] != dot[y2][x] for x in range(N)]))

    # Symbolic dot lookup
    def dlookup(a, b):
        result = IntVal(0)
        for y in range(N - 1, -1, -1):
            for x in range(N - 1, -1, -1):
                result = If(And(a == y, b == x), dot[y][x], result)
        return result

    # Retraction pair (mutual inverse on core)
    for x in core:
        solver.add(dlookup(r_var, dlookup(s_var, IntVal(x))) == x)
        solver.add(dlookup(s_var, dlookup(r_var, IntVal(x))) == x)
    solver.add(dlookup(r_var, IntVal(0)) == 0)  # anchor

    # Compute rep values: rep[k] = s^k(0)
    rep = [IntVal(0)]  # rep(0) = 0
    for k in range(1, N):
        rep.append(dlookup(s_var, rep[k - 1]))

    # Rep injectivity
    for i in range(N):
        for j in range(i + 1, N):
            solver.add(rep[i] != rep[j])

    # Strict self-simulation: dot(dot(t, rep(a)), rep(b)) = dot(a, b)
    for a in range(N):
        for b in range(N):
            lhs = dlookup(dlookup(t_var, rep[a]), rep[b])
            rhs = dot[a][b]
            solver.add(lhs == rhs)

    if require_D:
        # HasDichotomy (simplified: exists classifier, global dichotomy, non-degeneracy)
        cls = Int("cls")
        solver.add(cls >= 2, cls < N)
        for x in range(N):
            solver.add(Or(dlookup(cls, IntVal(x)) == 0, dlookup(cls, IntVal(x)) == 1))
        for y in core:
            all_abs = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
            all_core = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
            solver.add(Or(all_abs, all_core))
        solver.add(Or([And(dot[y][x] != 0, dot[y][x] != 1) for y in core for x in core]))

    if require_H:
        # HasICP
        a_icp = Int("a_icp")
        b_icp = Int("b_icp")
        c_icp = Int("c_icp")
        solver.add(a_icp >= 2, a_icp < N, b_icp >= 2, b_icp < N, c_icp >= 2, c_icp < N)
        solver.add(a_icp != b_icp, a_icp != c_icp, b_icp != c_icp)
        for x in core:
            solver.add(And(dlookup(b_icp, IntVal(x)) != 0, dlookup(b_icp, IntVal(x)) != 1))
        for x in core:
            solver.add(dlookup(a_icp, IntVal(x)) == dlookup(c_icp, dlookup(b_icp, IntVal(x))))
        solver.add(Or([dlookup(a_icp, IntVal(x)) != dlookup(a_icp, IntVal(y))
                       for x in core for y in core if x < y]))

    print(f"Searching N={N}, D={require_D}, H={require_H}...")
    result = solver.check()
    print(f"  Result: {result}")

    if result == sat:
        m = solver.model()
        s_val = m.evaluate(s_var).as_long()
        r_val = m.evaluate(r_var).as_long()
        t_val = m.evaluate(t_var).as_long()

        table = []
        for y in range(N):
            row = [m.evaluate(dot[y][x]).as_long() for x in range(N)]
            table.append(row)

        # Compute rep values
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

        # Check D
        for y in core:
            core_out = [table[y][x] for x in core]
            is_cls = all(v in (0, 1) for v in core_out)
            is_ncls = all(v not in (0, 1) for v in core_out)
            role = "classifier" if is_cls else ("non-classifier" if is_ncls else "MIXED")
            print(f"  Element {y}: {role} (core outputs: {core_out})")

        # Check which element t is
        t_core_out = [table[t_val][x] for x in core]
        t_is_cls = all(v in (0, 1) for v in t_core_out)
        print(f"  Simulation term t={t_val}: {'classifier' if t_is_cls else 'non-classifier'}")
        print(f"  t == s? {t_val == s_val}. t == r? {t_val == r_val}")

        return table, s_val, r_val, t_val, rep_vals
    return None


if __name__ == "__main__":
    print("=" * 60)
    print("PHASE 1: R only (no D, no H) + strict self-sim")
    print("=" * 60)
    for N in [5, 6]:
        search_strict_selfsim(N, require_D=False, require_H=False)
        print()

    print("=" * 60)
    print("PHASE 2: R+D+H + strict self-sim")
    print("=" * 60)
    for N in [5, 6, 7, 8]:
        result = search_strict_selfsim(N, require_D=True, require_H=True)
        print()
        if result:
            break

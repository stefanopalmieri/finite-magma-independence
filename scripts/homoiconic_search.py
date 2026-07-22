"""SAT search: judgment-of-codes laws over sorted S+D+C magmas.

World ∈ {swap, preserve}: sorted class-action of non-classifiers.
Blocks (WLOG up to iso): N-block = {2..2+m-1}, C-block = {2+m..n-1}.
  swap world:     |N| = |C| = m = (n-2)/2  (n even)
  preserve world: |N| = |C| = m chosen equal for comparability
s = 2, r = 3 (mutual inverse on core, anchored).
Baseline ICP: a = C0+1, b = s = 2, c = C0 (composition through quote).

Laws (τ ranges over the C-block; κ := C0 designated):
  L2A  quote-transparency, all judges:   τ·(s·x) = τ·x        on core
  L3A  quote-negation, all judges:       τ·(s·x) = 1 - τ·x    on core
  L4   sort-introspection:               κ·y = 0 iff y ∈ C-block (core y)
  L7   judge-closure under quote:        ∀τ ∃τ': τ'·x = τ·(s·x) on core
"""
import z3, itertools, sys

def build(n, world, laws, icp_through_quote=True):
    m = (n - 2) // 2
    Nblk = list(range(2, 2 + m))
    Cblk = list(range(2 + m, n))
    core = Nblk + Cblk
    T = [[z3.Int(f"t{i}_{j}") for j in range(n)] for i in range(n)]
    S = z3.Solver()
    for i in range(n):
        for j in range(n):
            S.add(T[i][j] >= 0, T[i][j] < n)
    # absorbers
    for j in range(n):
        S.add(T[0][j] == 0, T[1][j] == 1)
    # C-rows boolean on core; designated full classifier tau0 = C0
    for y in Cblk:
        for x in core:
            S.add(z3.Or(T[y][x] == 0, T[y][x] == 1))
    S.add(z3.Or(T[Cblk[0]][0] == 0, T[Cblk[0]][0] == 1))
    S.add(z3.Or(T[Cblk[0]][1] == 0, T[Cblk[0]][1] == 1))
    # N-rows sorted by world
    for y in Nblk:
        for x in core:
            tgt_blk = (Cblk if x in Nblk else Nblk) if world == "swap" else (Nblk if x in Nblk else Cblk)
            S.add(z3.Or([T[y][x] == v for v in tgt_blk]))
    # no other left absorbers
    for y in core:
        S.add(z3.Or([T[y][x] != y for x in range(n)]))
    # extensionality
    for a, b in itertools.combinations(range(n), 2):
        S.add(z3.Or([T[a][x] != T[b][x] for x in range(n)]))
    # retraction pair s=2, r=3 (mutual inverse on core; anchored)
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[3][v] == x))
            S.add(z3.Implies(T[3][x] == v, T[2][v] == x))
    S.add(T[3][0] == 0)
    # ICP: composition through quote (a, b, c) = (C1, 2, C0), or generic pair
    a_, b_, c_ = (Cblk[1], 2, Cblk[0]) if icp_through_quote else (Cblk[0], 2, Cblk[1])
    for x in core:
        for v in core:
            S.add(z3.Implies(T[b_][x] == v, T[a_][x] == T[c_][v]))
    S.add(z3.Or([T[a_][x] != T[a_][y] for x, y in itertools.combinations(core, 2)]))
    # laws
    if "L2A" in laws:
        for t in Cblk:
            for x in core:
                for v in core:
                    S.add(z3.Implies(T[2][x] == v, T[t][v] == T[t][x]))
    if "L3A" in laws:
        for t in Cblk:
            for x in core:
                for v in core:
                    S.add(z3.Implies(T[2][x] == v, T[t][v] == 1 - T[t][x]))
    if "L4" in laws:
        k = Cblk[0]
        for y in Cblk:
            S.add(T[k][y] == 0)
        for y in Nblk:
            S.add(T[k][y] == 1)
    if "L7" in laws:
        for t in Cblk:
            opts = []
            for t2 in Cblk:
                conj = []
                for x in core:
                    for v in core:
                        conj.append(z3.Implies(T[2][x] == v, T[t2][x] == T[t][v]))
                opts.append(z3.And(conj))
            S.add(z3.Or(opts))
    return S, T

def run(n, world, laws, icp_q=True):
    S, T = build(n, world, laws, icp_q)
    res = S.check()
    return res, (S.model() if res == z3.sat else None), T

def show(model, T, n):
    for i in range(n):
        print("   ", [model.evaluate(T[i][j]).as_long() for j in range(n)])

experiments = [
    ("baseline",            []),
    ("L2A transparency",    ["L2A"]),
    ("L3A negation",        ["L3A"]),
    ("L4 introspection",    ["L4"]),
    ("L7 closure",          ["L7"]),
    ("L2A + L4",            ["L2A", "L4"]),
    ("L3A + L4",            ["L3A", "L4"]),
    ("L3A + L4 + L7",       ["L3A", "L4", "L7"]),
]

print(f"{'experiment':22s}", "  ".join(f"{w}:{n}" for w in ("swap", "pres") for n in (6, 8, 10)))
results = {}
for name, laws in experiments:
    row = []
    for world in ("swap", "preserve"):
        for n in (6, 8, 10):
            res, model, T = run(n, world, laws)
            results[(name, world, n)] = (res, model, T)
            row.append("SAT " if res == z3.sat else "UNSAT")
    print(f"{name:22s}", "  ".join(f"{r:5s}" for r in row))

# the canonical homoiconic kernel at N=6: swap + L4 + L3A + closure
res, model, T = run(6, "swap", ["L4", "L3A", "L7"])
if res == z3.sat:
    print("\nCanonical homoiconic kernel, N=6 (swap + introspection + negation + closure):")
    show(model, T, 6)

# N=16 spot checks (the artifact size)
print("\nN=16 spot checks (swap world):")
for name, laws in [("baseline", []), ("L4", ["L4"]), ("L4+L3A", ["L4", "L3A"]), ("L4+L2A", ["L4", "L2A"])]:
    res, model, T = run(16, "swap", laws)
    print(f"  {name:10s}: {res}")

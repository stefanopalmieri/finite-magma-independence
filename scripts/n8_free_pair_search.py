"""N=8 artifact search: kernel stack + one free dual pair.

Roles (pinned WLOG): 0,1 halt; 2 = quote (s), 3 = eval (r); 4 = free
operator gamma; 5 = data? (kappa, introspection); 6 = judge? (= kappa.s);
7 = free judge. Blocks: N = {2,3,4}, C = {5,6,7}. Swap world.
"""
import z3, itertools

n = 8
Nblk, Cblk = [2, 3, 4], [5, 6, 7]
core = Nblk + Cblk

def base_solver():
    T = [[z3.Int(f"t{i}_{j}") for j in range(n)] for i in range(n)]
    S = z3.Solver()
    for i in range(n):
        for j in range(n):
            S.add(T[i][j] >= 0, T[i][j] < n)
    for j in range(n):
        S.add(T[0][j] == 0, T[1][j] == 1)
    # sorted swap world
    for y in Nblk:
        for x in core:
            S.add(z3.Or([T[y][x] == v for v in (Cblk if x in Nblk else Nblk)]))
    for y in Cblk:
        for x in core:
            S.add(z3.Or(T[y][x] == 0, T[y][x] == 1))
    # kappa = 5 is a full classifier (absorber columns boolean too), introspective
    S.add(z3.Or(T[5][0] == 0, T[5][0] == 1), z3.Or(T[5][1] == 0, T[5][1] == 1))
    for y in Cblk: S.add(T[5][y] == 0)
    for y in Nblk: S.add(T[5][y] == 1)
    # judge? = 6: the complement row on core — this IS the ICP law
    # (in the swap world with kappa pinned, the complement row equals
    # data? . quote pointwise). The explicit equation below is
    # REDUNDANT given the pinning; kept for documentation, verified
    # empirically in n8_enumerate_lexmin.py (168 models either way;
    # the full ICP ablation there: drop both -> 306 models, lex-min
    # unchanged).
    for y in Cblk: S.add(T[6][y] == 1)
    for y in Nblk: S.add(T[6][y] == 0)
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[6][x] == T[5][v]))
    # retraction pair (mutual, anchored)
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[3][v] == x))
            S.add(z3.Implies(T[3][x] == v, T[2][v] == x))
    S.add(T[3][0] == 0)
    # no other absorbers; extensionality
    for y in core:
        S.add(z3.Or([T[y][x] != y for x in range(n)]))
    for a, b in itertools.combinations(range(n), 2):
        S.add(z3.Or([T[a][x] != T[b][x] for x in range(n)]))
    return S, T

def s_pow_eq(T, k, x, target):
    """constraint: s^k(x) == target, via chained implications (returns list)."""
    cons = []
    def chain(depth, pos_var_pairs):
        # pos_var_pairs: list of (value chains) — build implications
        pass
    # direct encoding: enumerate all chains of length k over core
    out = []
    def rec(prefix):
        if len(prefix) == k + 1:
            ante = z3.And([T[2][prefix[i]] == prefix[i+1] for i in range(k)]) if k > 0 else z3.BoolVal(True)
            out.append(z3.Implies(ante, z3.BoolVal(prefix[-1] == target)))
            return
        last = prefix[-1]
        for v in core:
            rec(prefix + [v])
    rec([x])
    return out

def add_order(S, T, kind):
    # s-action on 6 core elts, block-crossing => cycle type (2,2,2), (4,2) or (6)
    if kind == 2:      # s^2 = id
        for x in core:
            for v in core:
                S.add(z3.Implies(T[2][x] == v, T[2][v] == x))
    elif kind == 4:    # s^4 = id, s^2 != id
        for x in core:
            for v in core:
                for w in core:
                    for u in core:
                        S.add(z3.Implies(z3.And(T[2][x] == v, T[2][v] == w, T[2][w] == u), T[2][u] == x))
        S.add(z3.Or([z3.And(T[2][x] == v, T[2][v] != x) for x in core for v in core]))
    elif kind == 6:    # not s^2 = id and not s^4 = id
        S.add(z3.Or([z3.And(T[2][x] == v, T[2][v] != x) for x in core for v in core]))
        opts = []
        for x in core:
            for v in core:
                for w in core:
                    for u in core:
                        opts.append(z3.And(T[2][x] == v, T[2][v] == w, T[2][w] == u, T[2][u] != x))
        S.add(z3.Or(opts))

def check(name, extra=None, order=None, ret_model=False):
    S, T = base_solver()
    if order: add_order(S, T, order)
    if extra: extra(S, T)
    res = S.check()
    print(f"  {name:46s}: {res}")
    if ret_model and res == z3.sat:
        return S.model(), T
    return None, T

print("== P0/P1: baseline and the code-assignment of the free operator ==")
check("baseline (kernel stack + free pair)")
for tgt in (5, 6, 7):
    check(f"s(gamma)=s(4) = {tgt}", lambda S, T, t=tgt: S.add(T[2][4] == t))
for tgt in (5, 6, 7):
    check(f"s(quote)=s(2) = {tgt}", lambda S, T, t=tgt: S.add(T[2][2] == t))

print("== P2: quote order (cycle type of s on the 6-element core) ==")
for k in (2, 4, 6):
    check(f"quote order {k}", order=k)

print("== P3: judge-closure L7 ==")
def closure(S, T):
    for t in Cblk:
        opts = []
        for t2 in Cblk:
            conj = []
            for x in core:
                for v in core:
                    conj.append(z3.Implies(T[2][x] == v, T[t2][x] == T[t][v]))
            opts.append(z3.And(conj))
        S.add(z3.Or(opts))
check("closure alone", closure)
for k in (2, 4, 6):
    check(f"closure + quote order {k}", closure, order=k)

print("== P4: the free judge's quotation law (forced or free?) ==")
def transparent7(S, T):
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[7][v] == T[7][x]))
def negating7(S, T):
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[7][v] == 1 - T[7][x]))
check("judge 7 quote-transparent", transparent7)
check("judge 7 quote-negating", negating7)

print("== P5: recognizer laws for the free pair ==")
def recognizer(S, T):
    # 7 answers z1=0 on everything gamma builds; and not everywhere
    for x in core:
        for v in core:
            S.add(z3.Implies(T[4][x] == v, T[7][v] == 0))
    S.add(z3.Or([T[7][y] == 1 for y in core]))
def injective_gamma(S, T):
    for x, y in itertools.combinations(core, 2):
        S.add(T[4][x] != T[4][y])
check("recognizer: 7 accepts Im(gamma), not all", recognizer)
check("recognizer + gamma injective", lambda S, T: (recognizer(S, T), injective_gamma(S, T)))
check("recognizer + injective + closure", lambda S, T: (recognizer(S, T), injective_gamma(S, T), closure(S, T)))

print("== P6: pairing wall (cons with car+cdr) — expect UNSAT ==")
def pairing(S, T):
    opts = []
    for p1 in core:
        for p2 in core:
            conj = []
            for x in core:
                for y in core:
                    for v in core + [0, 1]:      # gamma.x
                        for w in range(n):        # (gamma.x).y
                            conj.append(z3.Implies(z3.And(T[4][x] == v, T[v][y] == w),
                                                   z3.And(T[p1][w] == x, T[p2][w] == y)))
            opts.append(z3.And(conj))
    S.add(z3.Or(opts))
check("exists car,cdr with faithful curried cons", pairing)

print("== P7: how much freedom is left? (distinct core-subtables, capped) ==")
def count_core_models(extra=None, cap=200):
    S, T = base_solver()
    if extra: extra(S, T)
    seen = 0
    while seen < cap and S.check() == z3.sat:
        m = S.model()
        block = [T[i][j] != m.evaluate(T[i][j]).as_long() for i in core for j in core]
        S.add(z3.Or(block))
        seen += 1
    return seen
c0 = count_core_models()
c1 = count_core_models(lambda S, T: (recognizer(S, T), injective_gamma(S, T), closure(S, T)))
print(f"  baseline core-subtables: {c0}{'+' if c0 >= 200 else ''}")
print(f"  + recognizer/injective/closure: {c1}{'+' if c1 >= 200 else ''}")

print("== recommended artifact: full stack, one model ==")
m, T = check("full stack model", lambda S, T: (recognizer(S, T), injective_gamma(S, T), closure(S, T)), ret_model=True)
if m:
    for i in range(n):
        print("   ", [m.evaluate(T[i][j]).as_long() for j in range(n)])

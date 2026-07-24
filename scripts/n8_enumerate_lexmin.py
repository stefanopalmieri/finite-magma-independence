"""Reproducibility closure for the canonical N=8 artifact (Stack A).

`Magma/ArtifactN8.lean` claims: the full law set admits exactly 228
distinct core tables, and `rawA8` is the lexicographically minimal
one. The probe script (`n8_free_pair_search.py`) caps its model count
at 200 and does not perform the minimization, so this script is the
committed, uncapped derivation:

  1. encode the documented law set — kernel (swap world, classifier
     kappa with introspection, judge? = data? . quote, mutual anchored
     retraction, extensionality, no other absorbers) + faithful shift
     + hygiene (shift commutes with quote and eval, shift involution,
     shift distinct from quote and from eval) + judge-closure;
  2. enumerate ALL models, blocking on the core x core subtable
     (absorber rows are forced; core rows may vary off-core only in
     ways extensionality already separates) -> expect 228;
  3. extract the lexicographically minimal full table by greedy
     cell-by-cell minimization in row-major order (fix the smallest
     value for each cell that keeps the constraints satisfiable;
     greedy prefix-fixing IS lex-minimality) -> expect rawA8 exactly.

Roles pinned WLOG (the symmetry-breaking): 0,1 halt; 2 quote; 3 eval;
4 shift; 5 data?; 6 judge?; 7 free judge. "Lexicographically minimal"
is relative to this role labeling and row-major cell order.
"""
import itertools
import z3

n = 8
Nblk, Cblk = [2, 3, 4], [5, 6, 7]
core = Nblk + Cblk

RAW_A8 = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [0, 0, 5, 6, 7, 2, 3, 4],
    [0, 1, 5, 6, 7, 2, 3, 4],
    [0, 0, 5, 7, 6, 2, 4, 3],
    [0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 1, 0, 0, 1],
]


def law_set():
    T = [[z3.Int(f"t{i}_{j}") for j in range(n)] for i in range(n)]
    S = z3.Solver()
    for i in range(n):
        for j in range(n):
            S.add(T[i][j] >= 0, T[i][j] < n)
    # absorbers
    for j in range(n):
        S.add(T[0][j] == 0, T[1][j] == 1)
    # sorted swap world: operators send operators to judges and back;
    # judges answer in the halt channels
    for y in Nblk:
        for x in core:
            S.add(z3.Or([T[y][x] == v for v in (Cblk if x in Nblk else Nblk)]))
    for y in Cblk:
        for x in core:
            S.add(z3.Or(T[y][x] == 0, T[y][x] == 1))
    # kappa = 5: full classifier (boolean on absorber columns too),
    # introspective for the sort partition
    S.add(z3.Or(T[5][0] == 0, T[5][0] == 1), z3.Or(T[5][1] == 0, T[5][1] == 1))
    for y in Cblk:
        S.add(T[5][y] == 0)
    for y in Nblk:
        S.add(T[5][y] == 1)
    # judge? = 6: complement row on the core, and the ICP law
    # judge? = data? . quote
    for y in Cblk:
        S.add(T[6][y] == 1)
    for y in Nblk:
        S.add(T[6][y] == 0)
    for x in core:
        for v in core:
            S.add(z3.Implies(T[2][x] == v, T[6][x] == T[5][v]))
    # mutual anchored retraction (quote = 2, eval = 3)
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
    # faithful shift: gamma = 4 injective on the core
    for x, y in itertools.combinations(core, 2):
        S.add(T[4][x] != T[4][y])
    # hygiene: shift commutes with quote and with eval on the core
    for x in core:
        for v in core:
            for w in core:
                S.add(z3.Implies(z3.And(T[2][x] == v, T[4][x] == w),
                                 T[4][v] == T[2][w]))
                S.add(z3.Implies(z3.And(T[3][x] == v, T[4][x] == w),
                                 T[4][v] == T[3][w]))
    # hygiene: shift is an involution on the core
    for x in core:
        for v in core:
            S.add(z3.Implies(T[4][x] == v, T[4][v] == x))
    # shift acts differently from quote and from eval
    S.add(z3.Or([T[4][x] != T[2][x] for x in core]))
    S.add(z3.Or([T[4][x] != T[3][x] for x in core]))
    # judge-closure: for every judge t, t . quote is a named judge
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


def enumerate_core_tables():
    S, T = law_set()
    count = 0
    while S.check() == z3.sat:
        m = S.model()
        S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                     for i in core for j in core]))
        count += 1
    return count


def lex_min_table():
    S, T = law_set()
    fixed = []
    for i in range(n):
        row = []
        for j in range(n):
            for val in range(n):
                S.push()
                S.add(T[i][j] == val)
                if S.check() == z3.sat:
                    S.pop()
                    S.add(T[i][j] == val)  # fix permanently
                    row.append(val)
                    break
                S.pop()
            else:
                raise RuntimeError(f"no value satisfiable at cell ({i},{j})")
        fixed.append(row)
    return fixed


if __name__ == "__main__":
    count = enumerate_core_tables()
    print(f"distinct core tables under the full law set: {count}")
    tbl = lex_min_table()
    print("lexicographically minimal table (greedy, row-major):")
    for row in tbl:
        print("  ", row)
    assert count == 228, f"expected 228 core tables, got {count}"
    assert tbl == RAW_A8, "lex-min table does not match rawA8!"
    print("MATCH: count = 228 and lex-min table = rawA8 (ArtifactN8.lean)")

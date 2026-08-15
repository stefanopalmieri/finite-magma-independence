"""Reproducibility closure for the canonical N=8 artifact (Stack A).

`Magma/ArtifactN8.lean` claims: the full law set (including the
no-internal-dispatch law adopted 2026-08-01) admits exactly 168
distinct core tables, and `rawA8` is the lexicographically minimal
one; the pre-adoption law set admits 228 with the same lex-min. The probe script (`n8_free_pair_search.py`) caps its model count
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

ICP ablation (2026-08-14): the run below also records the selective
status of the ICP law, in the style of the ¬W and eval-commutation
records:
  - the ICP *equation* (judge? = data? . quote) is empirically
    redundant given the row-6 complement pinning: dropping it leaves
    168 models;
  - dropping the row-6 laws entirely (pinning + equation; row 6 then
    constrained only by the swap world, extensionality, judge-closure
    and ¬W) grows the space to 306 models with the lex-min artifact
    UNCHANGED. Moreover the ICP *property* still holds in every one
    of the 306: judge-closure at t = kappa forces some judge row to
    equal kappa . quote = 1 - chi (verified UNSAT below). So within
    the adopted law set ICP is a THEOREM of judge-closure + frame;
    the row-6 laws only add the labeling convention "the complement
    lives at element 6". The 306 vs 168 delta is bookkeeping, not
    capability;
  - judge-closure is the load-bearing law twice over: it implies the
    ICP property, and dropping it grows the space to 1860 and moves
    the lex-min at row 7 (shift? becomes [0,0,0,0,0,0,0,1] — the
    recognizer content of the free judge is bought by judge-closure,
    not emergent from lex-min).
Where ICP *is* consumed is the metacircular interpreter, not the
artifact derivation: Magma/KernelConsumption.lean.
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


def law_set(eval_comm=True, no_dispatch=True, icp_pin=True, icp_eq=True,
            closure=True):
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
    # judge? = 6: complement row on the core (this IS the ICP law:
    # in the swap world with kappa pinned, the complement row equals
    # data? . quote pointwise)
    if icp_pin:
        for y in Cblk:
            S.add(T[6][y] == 1)
        for y in Nblk:
            S.add(T[6][y] == 0)
    # The explicit composition equation judge? = data? . quote is
    # REDUNDANT given the pinning above (swap world + kappa pinning
    # already force T[5][T[2][x]] to be the complement of the sort
    # indicator); kept behind its own switch so the run below can
    # verify the redundancy empirically (168 models either way).
    if icp_eq:
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
    # hygiene: shift commutes with quote (and, if eval_comm, with eval —
    # Magma/EvalSideFree.lean proves the eval half REDUNDANT given the
    # mutual retraction; the run below verifies that empirically)
    for x in core:
        for v in core:
            for w in core:
                S.add(z3.Implies(z3.And(T[2][x] == v, T[4][x] == w),
                                 T[4][v] == T[2][w]))
                if eval_comm:
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
    if closure:
        for t in Cblk:
            opts = []
            for t2 in Cblk:
                conj = []
                for x in core:
                    for v in core:
                        conj.append(
                            z3.Implies(T[2][x] == v, T[t2][x] == T[t][v]))
                opts.append(z3.And(conj))
            S.add(z3.Or(opts))
    if no_dispatch:
        # The no-internal-dispatch law (adopted 2026-08-01 after the
        # W-probe, scripts/canonicality/probe_dispatch.py): no core row
        # is glued from two distinct core rows along an absorber-valued
        # core test with both branches realized where the handlers
        # disagree. Before adoption this was an unpriced consequence of
        # the lex-min tie-break (60 of the 228 pre-adoption models have
        # such a gluing); moving it into the law set restores the
        # tie-break to semantic inertness. The artifact is unchanged.
        gluings = []
        for d, h1, h2 in itertools.permutations(core, 3):
            for g in core:
                test = z3.And(*[z3.Or(T[g][x] == 0, T[g][x] == 1)
                                for x in core])
                route = z3.And(*[z3.And(
                    z3.Or(T[g][x] != 0, T[d][x] == T[h1][x]),
                    z3.Or(T[g][x] != 1, T[d][x] == T[h2][x]))
                    for x in core])
                live1 = z3.Or(*[z3.And(T[g][x] == 0, T[h1][x] != T[h2][x])
                                for x in core])
                live2 = z3.Or(*[z3.And(T[g][x] == 1, T[h1][x] != T[h2][x])
                                for x in core])
                gluings.append(z3.And(test, route, live1, live2))
        S.add(z3.Not(z3.Or(*gluings)))
    return S, T


def enumerate_core_tables(**kw):
    S, T = law_set(**kw)
    count = 0
    while S.check() == z3.sat:
        m = S.model()
        S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                     for i in core for j in core]))
        count += 1
    return count


def lex_min_table(**kw):
    S, T = law_set(**kw)
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
    assert count == 168, f"expected 168 core tables, got {count}"
    assert tbl == RAW_A8, "lex-min table does not match rawA8!"
    print("MATCH: count = 168 and lex-min table = rawA8 (ArtifactN8.lean)")
    # Pre-adoption record: without the no-dispatch law the space is 228
    # with the same lex-min (the historical derivation path).
    count0 = enumerate_core_tables(no_dispatch=False)
    print(f"without the no-dispatch law: {count0} core tables")
    assert count0 == 228, f"expected 228 pre-adoption, got {count0}"
    # Redundancy check (Magma/EvalSideFree.lean): dropping the
    # shift-commutes-with-eval law must not change the model space.
    count2 = enumerate_core_tables(eval_comm=False)
    print(f"without the eval-commutation law: {count2} core tables")
    assert count2 == 168, (
        f"eval-commutation law is NOT redundant: {count2} != 168")
    print("REDUNDANT: eval-commutation adds no constraint, as proved")
    # ICP ablation (2026-08-14). First: the explicit composition
    # equation is redundant given the row-6 complement pinning.
    count3 = enumerate_core_tables(icp_eq=False)
    print(f"without the ICP equation (pinning kept): {count3} core tables")
    assert count3 == 168, (
        f"ICP equation is NOT redundant given the pinning: {count3} != 168")
    print("REDUNDANT: the ICP equation adds no constraint over the pinning")
    # Second: dropping ICP entirely grows the space but leaves the
    # lex-min artifact bit-identical — ICP is chosen, and inert for
    # the artifact (it holds emergently: artifactA8_icp_through_quote).
    count4 = enumerate_core_tables(icp_pin=False, icp_eq=False)
    print(f"without ICP entirely (row 6 free): {count4} core tables")
    assert count4 == 306, f"expected 306 ICP-free core tables, got {count4}"
    tbl4 = lex_min_table(icp_pin=False, icp_eq=False)
    assert tbl4 == RAW_A8, "ICP-free lex-min table does not match rawA8!"
    print("INERT: ICP-free lex-min table = rawA8 — the artifact is unmoved")
    # ...and the ICP property survives in all 306: judge-closure at
    # t = kappa forces a complement row. UNSAT = no counterexample.
    S4, T4 = law_set(icp_pin=False, icp_eq=False)
    S4.add(z3.Not(z3.Or(*[
        z3.And(*[T4[r][x] == (0 if x in Nblk else 1) for x in core])
        for r in (6, 7)])))
    assert S4.check() == z3.unsat, (
        "found a pinning-free model with NO complement row — "
        "judge-closure does NOT imply ICP?!")
    print("DERIVED: every pinning-free model still carries the complement "
          "row — ICP is a consequence of judge-closure + frame")
    # Third: judge-closure IS load-bearing for the artifact — dropping
    # it moves the lex-min at row 7 (the free judge loses its shift?
    # recognizer content). The 'emergent' recognizer is bought by
    # judge-closure, not by the tie-break.
    count5 = enumerate_core_tables(closure=False)
    print(f"without judge-closure: {count5} core tables")
    assert count5 == 1860, f"expected 1860 closure-free core tables, got {count5}"
    tbl5 = lex_min_table(closure=False)
    assert tbl5[:7] == RAW_A8[:7] and tbl5[7] == [0, 0, 0, 0, 0, 0, 0, 1], (
        f"closure-free lex-min changed unexpectedly: {tbl5}")
    print("LOAD-BEARING: without judge-closure the lex-min moves at row 7")

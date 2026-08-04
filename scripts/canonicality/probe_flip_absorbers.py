"""Probes for docs/lawvere-diagonal-and-the-walls.md.

Probe 1 — total transposition-refusal of the artifact: which columns of
the N=8 table are named by a row?  `d_leaves_a_column_unnamed`
(CompletenessWall.lean) guarantees >= 1 unnamed column in any dichotomic
2-pointed structure; this measures the artifact exactly.
Result: all eight columns are unnamed.

Probe 2 — finite satisfiability of the wall's internalization
hypothesis: does any finite magma with two distinct left absorbers name
all of its columns (hflip: forall a exists m forall x, m.x = x.a)?
Result: UNSAT for n = 2..8 — machine evidence for the finite flip wall
(proved by hand in the note, all n): at finite scale the dichotomy D is
not needed; two absorbers alone refuse the flip.

Method for probe 2: any name m of column a satisfies m.z = z for both
absorbers z (since col_a(z) = z.a = z), so names lie in the core.
Enumerate assignments sigma: A -> core (sigma[a] = the name of column
a); each imposes the cell equalities table[sigma(a)][x] = table[x][a].
Under union-find over core-row cells (absorber rows are constants) an
assignment is realizable iff no equivalence class receives two distinct
constants; free classes may take any value.  SAT iff some sigma is
consistent.  Exhaustive for the sizes probed (|core|^n assignments).
"""

from itertools import product

A8 = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [0, 0, 5, 6, 7, 2, 3, 4],
    [0, 1, 5, 6, 7, 2, 3, 4],
    [0, 0, 5, 7, 6, 2, 4, 3],
    [0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 1, 0, 0, 1],
]


def probe_columns_named():
    rows = [tuple(r) for r in A8]
    named, unnamed = [], []
    for a in range(8):
        col = tuple(A8[x][a] for x in range(8))
        (named if col in rows else unnamed).append(a)
    return named, unnamed


def flip_two_absorbers_sat(n):
    """SAT iff some magma on n elements with left absorbers 0, 1 names
    every column with a row."""
    if n < 3:
        return False, None  # core empty; column 0 already unnameable
    core = list(range(2, n))
    for sigma in product(core, repeat=n):
        parent = {}

        def find(c):
            while parent.get(c, c) != c:
                parent[c] = parent.get(parent[c], parent[c])
                c = parent[c]
            return c

        def union(c, d):
            rc, rd = find(c), find(d)
            if rc != rd:
                parent[rc] = rd

        const = {}
        ok = True
        for a in range(n):
            m = sigma[a]
            for x in range(n):
                if x < 2:
                    r = find((m, x))
                    if const.get(r, x) != x:
                        ok = False
                        break
                    const[r] = x
                else:
                    union((m, x), (x, a))
            if not ok:
                break
        if not ok:
            continue
        merged, clash = {}, False
        for c, v in const.items():
            r = find(c)
            if merged.get(r, v) != v:
                clash = True
                break
            merged[r] = v
        if not clash:
            return True, sigma
    return False, None


if __name__ == "__main__":
    named, unnamed = probe_columns_named()
    print(f"Probe 1 (N=8 artifact): columns named by a row: {named}")
    print(f"                        columns named by NO row: {unnamed}")
    assert named == [], "artifact expected to internalize no column"

    for n in range(2, 9):
        sat, wit = flip_two_absorbers_sat(n)
        tag = f"SAT, witness sigma={wit}" if sat else "UNSAT"
        print(f"Probe 2: n={n}: hflip + two left absorbers {tag}")
        assert not sat, "finite flip wall predicts UNSAT at every finite n"
    print("Both probes agree with the note: total refusal at N=8; "
          "flip + two absorbers UNSAT for n <= 8.")

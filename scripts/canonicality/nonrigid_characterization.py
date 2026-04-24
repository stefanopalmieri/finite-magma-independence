"""
Characterize non-rigid strong-R + D + H magmas at N=6.

From enumerate_rdh_nonrigid_N6_strongR.json (100 classes, complete):
  - 99 classes have |Aut|=2 with sigma swapping absorbers (σ(0)=1, σ(1)=0).
  - 1 class has |Aut|=6 with sigma fixing absorbers and a 3-cycle on core
    (the automorphism group is S_3, containing both 3-cycles and involutions).

Conjecture: every non-rigid strong-R+D+H magma at N=6 has an automorphism σ
that either
   (A) swaps absorbers: σ(0)=1, σ(1)=0, or
   (B) is an absorber-fixing 3-cycle.

We verify via Z3 UNSAT:

  (NR.1) Every automorphism of a strong-R+D+H magma at N=6 permutes {0,1}.
         (Negation: ∃ E2PM + aut σ with σ(0) ∉ {0,1}.)

  (NR.2) Every non-rigid strong-R+D+H magma at N=6 has an automorphism of
         type (A) or (B) above.
         (Negation: ∃ T + non-trivial aut σ + NO aut of T has type A + NO
         aut of T has type B.  Encoded by enumerating the finite list of
         type-A and type-B permutations and asserting each is not an aut.)
"""

from __future__ import annotations

import itertools
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unknown, unsat


N = 6
CORE = list(range(2, N))
TIMEOUT_MS = 300_000


def make_solver():
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    return s


def add_E2PM_strong_R_D_H(s):
    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
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

    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if sv == rv:
                    continue
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx))
        s.add(Or(srx))

    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    tau_cases = [And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
                 for tv in CORE]
    s.add(Or(*tau_cases))

    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))

    return T


def add_aut_sigma(s, T, sigma):
    """Require sigma to be a (possibly trivial) permutation automorphism of T."""
    s.add(Distinct(*sigma))
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    for a in range(N):
        for b in range(N):
            big = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big.append(And(sigma[a] == sa, sigma[b] == sb,
                                       T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))


def sigma_power_equals_identity(s, sigma, k, name):
    """Add aux vars and constraints so that (sigma^k == identity) is expressed
    by a Boolean flag returned to the caller, so we can assert == or !=.
    Returns Bool expression 'sigma^k == id'."""
    # Build sigma_powers[0] = identity, sigma_powers[i] = sigma applied i times
    cur = [Int(f"{name}_p1_{i}") for i in range(N)]
    for i in range(N):
        s.add(cur[i] == sigma[i])
    for step in range(2, k + 1):
        nxt = [Int(f"{name}_p{step}_{i}") for i in range(N)]
        for i in range(N):
            # nxt[i] = sigma(cur[i])
            s.add(Or(*[And(cur[i] == j, nxt[i] == sigma[j]) for j in range(N)]))
        cur = nxt
    return And(*[cur[i] == i for i in range(N)])


def run_check(label, setup, print_witness=False):
    s = make_solver()
    T_holder, sigma_holder = setup(s)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == unsat:
        print(f"  [{dt:6.2f}s] UNSAT -- '{label}' holds")
        return True
    if r == sat:
        print(f"  [{dt:6.2f}s] SAT   -- '{label}' FAILS")
        if print_witness and T_holder is not None:
            m = s.model()
            table = [[m.eval(T_holder[a][b]).as_long() for b in range(N)] for a in range(N)]
            print("    Counterexample T:")
            for row in table:
                print(f"      {row}")
            if sigma_holder is not None:
                sig = [m.eval(sigma_holder[i]).as_long() for i in range(N)]
                print(f"    witness sigma = {sig}")
        return False
    print(f"  [{dt:6.2f}s] UNKNOWN -- '{label}'")
    return None


def enumerate_type_A_perms():
    """All absorber-swapping permutations of Fin(N): σ(0)=1, σ(1)=0, σ|core
    an arbitrary permutation of core."""
    out = []
    for p in itertools.permutations(CORE):
        tau = [1, 0] + list(p)
        out.append(tau)
    return out


def enumerate_type_B_perms():
    """All absorber-fixing 3-cycle permutations of Fin(N): σ(0)=0, σ(1)=1,
    σ|core is a 3-cycle (fixes one core element, rotates the other 3)."""
    out = []
    for fixed in CORE:
        others = [c for c in CORE if c != fixed]
        # Two orientations of a 3-cycle on the 3 elements in `others`.
        for rot in [(0, 1, 2), (0, 2, 1)]:
            # rot[i] says where others[i] goes (index within `others`).
            # Build tau: tau[0]=0, tau[1]=1, tau[fixed]=fixed, tau[others[i]]=others[rot[i]].
            tau = [0] * N
            tau[0] = 0
            tau[1] = 1
            tau[fixed] = fixed
            for i in range(3):
                tau[others[i]] = others[rot[i]]
            # Skip identity (which happens when rot is (0,1,2) — wait, that's identity on 3-cycle positions?)
            # rot=(0,1,2) means others[i] -> others[rot[i]] = others[i], identity. Skip.
            # rot=(0,2,1) means others[0]->others[0]=fixed mapping, but we fix `fixed` separately...
            # Let me redo this.
            pass
    # Cleaner: enumerate all permutations of core, keep those that are 3-cycles
    # (cycle structure: one fixed point + one 3-cycle).
    from itertools import permutations
    out = []
    for perm in permutations(CORE):
        # perm[i] is where CORE[i] goes
        mapping = dict(zip(CORE, perm))
        # compute cycle structure
        visited = set()
        cycles = []
        for c in CORE:
            if c in visited:
                continue
            cycle = []
            cur = c
            while cur not in visited:
                visited.add(cur)
                cycle.append(cur)
                cur = mapping[cur]
            cycles.append(cycle)
        cycle_lens = sorted(len(x) for x in cycles)
        if cycle_lens == [1, 3]:  # one fixed point + one 3-cycle
            tau = [0] * N
            tau[0] = 0
            tau[1] = 1
            for c in CORE:
                tau[c] = mapping[c]
            out.append(tau)
    return out


def assert_not_aut_of(s, T, tau):
    """Assert that the permutation tau (Python list of ints) is NOT an
    automorphism of T: ∃ (a,b) with tau[T[a][b]] != T[tau[a]][tau[b]]."""
    disjuncts = []
    for a in range(N):
        for b in range(N):
            # For each possible value v of T[a][b], if T[a][b] == v then tau[v] is
            # the image; require T[tau[a]][tau[b]] != tau[v] for some v hit.
            per_cell = []
            for v in range(N):
                per_cell.append(And(T[a][b] == v, T[tau[a]][tau[b]] != tau[v]))
            disjuncts.append(Or(*per_cell))
    s.add(Or(*disjuncts))


def main():
    print("=" * 72)
    print("Non-rigid characterization at N=6 (strong R + D + H)")
    print("=" * 72)

    print("\n(NR.1) Every automorphism of a strong-R+D+H magma at N=6 permutes {0,1}:")
    def setup_nr1(s):
        T = add_E2PM_strong_R_D_H(s)
        sigma = [Int(f"sigma_{i}") for i in range(N)]
        add_aut_sigma(s, T, sigma)
        s.add(Or(*[sigma[i] != i for i in range(N)]))  # non-trivial
        s.add(sigma[0] != 0, sigma[0] != 1)  # σ(0) ∉ {0, 1}
        return T, sigma
    run_check("aut permutes {0,1}", setup_nr1)

    type_A = enumerate_type_A_perms()
    type_B = enumerate_type_B_perms()
    print(f"\n  |type A (absorber-swapping)| = {len(type_A)}")
    print(f"  |type B (absorber-fixing 3-cycles)| = {len(type_B)}")

    print("\n(NR.2) Every non-rigid strong-R+D+H magma at N=6 has a type-A or type-B automorphism:")
    def setup_nr2(s):
        T = add_E2PM_strong_R_D_H(s)
        sigma = [Int(f"sigma_{i}") for i in range(N)]
        add_aut_sigma(s, T, sigma)
        s.add(Or(*[sigma[i] != i for i in range(N)]))
        for tau in type_A:
            assert_not_aut_of(s, T, tau)
        for tau in type_B:
            assert_not_aut_of(s, T, tau)
        return T, sigma
    run_check("non-rigid ⇒ has type-A or type-B aut", setup_nr2, print_witness=True)


if __name__ == "__main__":
    main()

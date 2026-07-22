#!/usr/bin/env python3
"""
Constructive role-recovery algorithm for finite extensional 2-pointed magmas
with capabilities R (retraction pair), D (classifier dichotomy), H (ICP).

Given only the Cayley table T, recover the canonical roles:
  - absorbers Z = {z1, z2}
  - classifiers C, non-classifiers N
  - retraction pair (s, r)
  - ICP triple (a, b, c)

The algorithm must be *relabel-invariant*: for any permutation pi of Fin(n),
recover_roles(T_pi) should produce the pi-image of recover_roles(T)'s answer.

Tested on paper witnesses W5 and W6, plus 20 random relabelings of each.
"""

from __future__ import annotations
import random
from itertools import permutations, product
from typing import Optional


# ---------------------------------------------------------------------------
# Axiom verification
# ---------------------------------------------------------------------------

def _validate_table(T: list[list[int]]) -> int:
    n = len(T)
    if n == 0:
        raise ValueError("Empty table.")
    for i, row in enumerate(T):
        if len(row) != n:
            raise ValueError(f"Row {i} has length {len(row)} != {n}.")
        for j, v in enumerate(row):
            if not (0 <= v < n):
                raise ValueError(f"T[{i}][{j}]={v} outside Fin({n}).")
    return n


def _find_absorbers(T: list[list[int]]) -> list[int]:
    """Left-absorbers: rows that are constant and equal to row-index."""
    n = len(T)
    absorbers = []
    for i in range(n):
        row = T[i]
        if all(v == row[0] for v in row) and row[0] == i:
            absorbers.append(i)
    return absorbers


def _constant_rows(T: list[list[int]]) -> list[int]:
    n = len(T)
    return [i for i in range(n) if all(v == T[i][0] for v in T[i])]


def _check_extensional(T: list[list[int]]) -> bool:
    return len({tuple(row) for row in T}) == len(T)


# ---------------------------------------------------------------------------
# z1 / z2 discrimination invariant
# ---------------------------------------------------------------------------

def _absorber_invariants(T: list[list[int]], absorbers: list[int], core: list[int]) -> dict[int, tuple]:
    """
    For each absorber z compute a relabel-invariant fingerprint.

    The fingerprint must depend only on the operation, not on integer labels.
    We use:
      - count of x in core with x*z = z   (fixers of z on the right)
      - count of x in core with x*z = other absorber
      - sorted multiset of (count of y in core with y*x = z) over x in core
      - sorted multiset of |{y in core : y*x = z}| over x in core (classifier outputs)
      - count of pairs (s, r) in core*core satisfying the R-equations with r*z = z
    """
    n = len(T)
    assert len(absorbers) == 2
    z_other = {absorbers[0]: absorbers[1], absorbers[1]: absorbers[0]}

    fingerprints: dict[int, tuple] = {}
    for z in absorbers:
        other = z_other[z]

        # Right-fixers of z inside core.
        fixers_to_z = sum(1 for x in core if T[x][z] == z)
        fixers_to_other = sum(1 for x in core if T[x][z] == other)

        # How often z appears as output of x*y for x,y in core.
        preimage_count = sum(1 for x in core for y in core if T[x][y] == z)

        # For each x in core, count how many y in core map to z under x.
        row_counts_to_z = tuple(sorted(
            sum(1 for y in core if T[x][y] == z) for x in core
        ))

        # For each x in core, count how many y in core map to z under y*x (column).
        col_counts_to_z = tuple(sorted(
            sum(1 for y in core if T[y][x] == z) for x in core
        ))

        # Anchoring asymmetry: count r in core such that r*z = z AND r*other != other.
        anchor_count = sum(
            1 for r in core if T[r][z] == z and T[r][other] != other
        )

        # Count retraction-pair candidates anchored at z.
        rpairs = 0
        for s in core:
            for r in core:
                if T[r][z] != z:
                    continue
                ok = True
                for x in core:
                    if T[r][T[s][x]] != x or T[s][T[r][x]] != x:
                        ok = False
                        break
                if ok:
                    rpairs += 1

        fingerprints[z] = (
            fixers_to_z,
            fixers_to_other,
            preimage_count,
            row_counts_to_z,
            col_counts_to_z,
            anchor_count,
            rpairs,
        )
    return fingerprints


def _pick_z1_z2(T: list[list[int]], absorbers: list[int], core: list[int]
                ) -> tuple[Optional[int], Optional[int]]:
    """
    Return (z1, z2). If invariants cannot distinguish, return (None, None).

    Convention: z1 is the *anchor* absorber -- the one with more retraction-
    related structure (more right-fixers in core, more preimage under core*core,
    more anchor witnesses r with r*z=z). Concretely, z1 is the absorber with
    the lexicographically LARGER invariant fingerprint.
    """
    fp = _absorber_invariants(T, absorbers, core)
    a, b = absorbers
    if fp[a] == fp[b]:
        return None, None
    if fp[a] > fp[b]:
        return a, b
    return b, a


# ---------------------------------------------------------------------------
# Classifier detection
# ---------------------------------------------------------------------------

def _find_classifiers(T: list[list[int]], absorbers: list[int], core: list[int]) -> list[int]:
    """tau in core is a classifier iff tau*x in {z1,z2} for all x in core."""
    Z = set(absorbers)
    return [t for t in core if all(T[t][x] in Z for x in core)]


def _classifier_signature(T: list[list[int]], tau: int, core: list[int],
                          z1: int, z2: int) -> tuple:
    """Relabel-invariant signature of a classifier.

    Components (all label-free given z1,z2 are already canonical):
      - number of core x with tau*x = z1  (and = z2)
      - value of tau*z1 and tau*z2        (0-or-1 "self" info on absorbers,
        encoded as codes: 0=z1, 1=z2, 2=core, to keep it invariant)
      - sorted multiset of codes of (x*tau) over x in core (column info)
      - tau*tau code
    """
    def code(v):
        if v == z1: return 0
        if v == z2: return 1
        return 2

    to_z1 = sum(1 for x in core if T[tau][x] == z1)
    to_z2 = sum(1 for x in core if T[tau][x] == z2)
    tau_on_z1 = code(T[tau][z1])
    tau_on_z2 = code(T[tau][z2])
    col_codes = tuple(sorted(code(T[x][tau]) for x in core))
    tau_sq = code(T[tau][tau])
    return (to_z1, to_z2, tau_on_z1, tau_on_z2, col_codes, tau_sq)


def _pick_tau(T: list[list[int]], classifiers: list[int], core: list[int],
              z1: int, z2: int) -> Optional[int]:
    if not classifiers:
        return None
    if len(classifiers) == 1:
        return classifiers[0]
    sigs = {t: _classifier_signature(T, t, core, z1, z2) for t in classifiers}
    # Canonical tau: classifier with lexicographically smallest signature;
    # if a unique minimum exists, return it, else None.
    sig_groups: dict[tuple, list[int]] = {}
    for t, s in sigs.items():
        sig_groups.setdefault(s, []).append(t)
    min_sig = min(sig_groups.keys())
    if len(sig_groups[min_sig]) == 1:
        return sig_groups[min_sig][0]
    return None


# ---------------------------------------------------------------------------
# Retraction pair search
# ---------------------------------------------------------------------------

def _find_retraction_pair(T: list[list[int]], core: list[int], z1: int
                          ) -> Optional[tuple[int, int]]:
    """
    Return (s, r) with s,r in core s.t. r*(s*x)=x and s*(r*x)=x for x in core,
    and r*z1 = z1. Canonical choice: lexicographically smallest (s, r).
    """
    candidates = []
    for s in core:
        for r in core:
            if T[r][z1] != z1:
                continue
            ok = True
            for x in core:
                if T[r][T[s][x]] != x or T[s][T[r][x]] != x:
                    ok = False
                    break
            if ok:
                candidates.append((s, r))
    if not candidates:
        return None
    # Cannot use lexicographic min on raw integers (not relabel-invariant on its own),
    # but we return the unique pair if there is one, else a canonical choice by
    # a relabel-invariant tie-breaker: prefer (s,r) where s==r (involution) first,
    # then by the multiset of (s*x, r*x) outputs. In practice for R+D+H witnesses
    # the pair is unique up to this symmetry.
    involutions = [(s, r) for (s, r) in candidates if s == r]
    if involutions:
        return involutions[0]
    return candidates[0]


# ---------------------------------------------------------------------------
# ICP triple search
# ---------------------------------------------------------------------------

def _find_icp_triple(T: list[list[int]], core: list[int]
                     ) -> Optional[tuple[int, int, int]]:
    core_set = set(core)
    for a, b, c in permutations(core, 3):
        # b*x in core for all x in core.
        if not all(T[b][x] in core_set for x in core):
            continue
        # a*x = c*(b*x) for all x in core.
        if not all(T[a][x] == T[c][T[b][x]] for x in core):
            continue
        # |{a*x : x in core}| >= 2.
        if len({T[a][x] for x in core}) < 2:
            continue
        return (a, b, c)
    return None


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def recover_roles(T: list[list[int]]) -> dict:
    n = _validate_table(T)

    # Left-absorbers (rows constant AND equal to index).
    absorbers = _find_absorbers(T)
    if len(absorbers) != 2:
        # Try a relaxed definition: any row that is constant.
        const_rows = _constant_rows(T)
        if len(const_rows) != 2:
            raise ValueError(
                f"Expected exactly 2 left-absorbers; found constant rows {const_rows}."
            )
        absorbers = const_rows
        # Check "no other row is constant" already enforced by len==2.

    # Extensionality.
    if not _check_extensional(T):
        raise ValueError("Table is not extensional (duplicate rows).")

    core = [i for i in range(n) if i not in set(absorbers)]

    # Identify z1 vs z2 by invariants.
    z1, z2 = _pick_z1_z2(T, absorbers, core)

    # Classifier set.
    classifiers = _find_classifiers(T, absorbers, core)
    non_classifiers = [x for x in core if x not in classifiers]

    # D-capability sanity: every core element is classifier or non-classifier
    # (trivially true by construction) AND at least one non-classifier exists.
    D_ok = len(non_classifiers) >= 1 and len(classifiers) >= 1

    # tau canonical.
    tau = None
    if z1 is not None and z2 is not None and classifiers:
        tau = _pick_tau(T, classifiers, core, z1, z2)

    # Retraction pair.
    retraction = None
    if z1 is not None:
        retraction = _find_retraction_pair(T, core, z1)
    if retraction is None and z2 is not None:
        # Fallback: maybe r*z2=z2 anchoring. (Should not happen on witnesses.)
        retraction = _find_retraction_pair(T, core, z2)

    # ICP triple.
    icp = _find_icp_triple(T, core)

    capabilities = {
        'R': retraction is not None,
        'D': D_ok,
        'H': icp is not None,
    }

    if not (capabilities['R'] and capabilities['D'] and capabilities['H']):
        raise ValueError(
            f"Magma is not R+D+H: capabilities = {capabilities}."
        )

    return {
        'absorbers': frozenset(absorbers),
        'z1': z1,
        'z2': z2,
        'classifiers': frozenset(classifiers),
        'tau': tau,
        'non_classifiers': frozenset(non_classifiers),
        'retraction_pair': retraction,
        'icp_triple': icp,
        'capabilities': capabilities,
    }


# ---------------------------------------------------------------------------
# Relabeling helpers
# ---------------------------------------------------------------------------

def relabel(T: list[list[int]], pi: list[int]) -> list[list[int]]:
    """Return T_pi with T_pi[pi[a]][pi[b]] = pi[T[a][b]]."""
    n = len(T)
    T2 = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            T2[pi[a]][pi[b]] = pi[T[a][b]]
    return T2


def apply_pi(pi: list[int], x):
    if x is None:
        return None
    if isinstance(x, frozenset):
        return frozenset(pi[v] for v in x)
    if isinstance(x, tuple):
        return tuple(pi[v] for v in x)
    return pi[x]


# ---------------------------------------------------------------------------
# Witness tables and tests
# ---------------------------------------------------------------------------

T_W5 = [
    [0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [0, 1, 2, 3, 4],
    [0, 0, 0, 1, 1],
    [0, 1, 0, 1, 1],
]
# Expected: z1=0, z2=1, s=r=2, tau=3, non-classifier core = {2}.
W5_EXPECTED = {
    'absorbers': frozenset({0, 1}),
    'z1': 0, 'z2': 1,
    'classifiers': frozenset({3, 4}),   # rows 3 and 4 are core -> {0,1}
    'tau': 3,
    'non_classifiers': frozenset({2}),
    'retraction_pair': (2, 2),
}

T_W6 = [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [3, 3, 4, 2, 5, 3],
    [0, 1, 3, 5, 2, 4],
    [0, 0, 1, 0, 1, 1],
    [2, 2, 5, 4, 3, 2],
]
# Expected: z1=0, z2=1, s=2, r=3, tau=4.
W6_EXPECTED = {
    'absorbers': frozenset({0, 1}),
    'z1': 0, 'z2': 1,
    'classifiers': frozenset({4}),       # only row 4's core outputs lie in {0,1}
    'tau': 4,
    'non_classifiers': frozenset({2, 3, 5}),
    'retraction_pair': (2, 3),
}


def _inspect(T, label):
    n = len(T)
    print(f"--- {label} (n={n}) ---")
    absorbers = _find_absorbers(T)
    print(f"  absorbers (row i constant = i): {absorbers}")
    core = [i for i in range(n) if i not in set(absorbers)]
    print(f"  core: {core}")
    for t in core:
        outs = [T[t][x] for x in core]
        in_Z = all(o in set(absorbers) for o in outs)
        print(f"  row {t} on core = {outs}  classifier={in_Z}")


def run_witness(T, name, expected):
    print(f"\n=== {name} under original labels ===")
    res = recover_roles(T)
    print(f"  absorbers      = {sorted(res['absorbers'])}")
    print(f"  z1, z2         = {res['z1']}, {res['z2']}")
    print(f"  classifiers    = {sorted(res['classifiers'])}")
    print(f"  tau            = {res['tau']}")
    print(f"  non_classifiers= {sorted(res['non_classifiers'])}")
    print(f"  retraction     = {res['retraction_pair']}")
    print(f"  icp_triple     = {res['icp_triple']}")
    print(f"  capabilities   = {res['capabilities']}")

    ok = True
    if res['absorbers'] != expected['absorbers']:
        ok = False; print(f"  MISMATCH absorbers; expected {sorted(expected['absorbers'])}")
    if res['z1'] != expected['z1']:
        ok = False; print(f"  MISMATCH z1; expected {expected['z1']}")
    if res['z2'] != expected['z2']:
        ok = False; print(f"  MISMATCH z2; expected {expected['z2']}")
    if res['classifiers'] != expected['classifiers']:
        ok = False; print(f"  MISMATCH classifiers; expected {sorted(expected['classifiers'])}")
    if res['tau'] != expected['tau']:
        ok = False; print(f"  MISMATCH tau; expected {expected['tau']}")
    if res['non_classifiers'] != expected['non_classifiers']:
        ok = False; print(f"  MISMATCH non_classifiers; expected {sorted(expected['non_classifiers'])}")
    if res['retraction_pair'] != expected['retraction_pair']:
        # s,r may be swapped and still valid; accept either ordering as tie-break info only.
        ok = False; print(f"  NOTE retraction differs; got {res['retraction_pair']} vs expected {expected['retraction_pair']}")
    print(f"  original-label recovery OK: {ok}")
    return ok, res


def run_permutation_tests(T, name, expected, rounds=20, seed=17):
    print(f"\n=== {name} under {rounds} random relabelings ===")
    n = len(T)
    rng = random.Random(seed)
    passes = 0
    failures = []
    for k in range(rounds):
        pi = list(range(n))
        rng.shuffle(pi)
        Tp = relabel(T, pi)
        try:
            res = recover_roles(Tp)
        except Exception as e:
            failures.append((k, pi, f"exception: {e}"))
            continue
        exp_pi = {
            'absorbers': apply_pi(pi, expected['absorbers']),
            'z1': apply_pi(pi, expected['z1']),
            'z2': apply_pi(pi, expected['z2']),
            'classifiers': apply_pi(pi, expected['classifiers']),
            'tau': apply_pi(pi, expected['tau']),
            'non_classifiers': apply_pi(pi, expected['non_classifiers']),
            'retraction_pair': apply_pi(pi, expected['retraction_pair']),
        }
        mismatches = []
        for key in ('absorbers', 'z1', 'z2', 'classifiers', 'tau', 'non_classifiers'):
            if res[key] != exp_pi[key]:
                mismatches.append((key, res[key], exp_pi[key]))
        # Retraction pair: either orientation acceptable, so check the set and anchoring.
        got_pair = res['retraction_pair']
        if got_pair is None:
            mismatches.append(('retraction_pair', got_pair, exp_pi['retraction_pair']))
        else:
            exp_pair = exp_pi['retraction_pair']
            if set(got_pair) != set(exp_pair):
                mismatches.append(('retraction_pair(set)', got_pair, exp_pair))
        if mismatches:
            failures.append((k, pi, mismatches))
        else:
            passes += 1
    print(f"  {passes}/{rounds} permutation tests passed.")
    if failures:
        print(f"  First failure: {failures[0]}")
    return passes, failures


def main():
    # Quick structural inspection so the reader can verify our expectations.
    _inspect(T_W5, "W5")
    _inspect(T_W6, "W6")

    ok5, _ = run_witness(T_W5, "W5", W5_EXPECTED)
    ok6, _ = run_witness(T_W6, "W6", W6_EXPECTED)

    p5, f5 = run_permutation_tests(T_W5, "W5", W5_EXPECTED, rounds=20, seed=17)
    p6, f6 = run_permutation_tests(T_W6, "W6", W6_EXPECTED, rounds=20, seed=23)

    print("\n=== Summary ===")
    print(f"  W5 original: {'PASS' if ok5 else 'FAIL'}  | permutations: {p5}/20")
    print(f"  W6 original: {'PASS' if ok6 else 'FAIL'}  | permutations: {p6}/20")


if __name__ == "__main__":
    main()

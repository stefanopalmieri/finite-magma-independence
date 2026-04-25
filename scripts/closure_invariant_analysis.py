"""
Structural analysis of the row-image partial-monoid closure-count invariant.

Three questions:

  1. Iso-invariance: confirm closure count is invariant under
     absorber-preserving permutations (permutations fixing {0,1} as a set).
  2. Structural characterization of the 2/4/5 split at N=5: classify magmas
     by the action-on-core of the unique non-classifier g, correlate with
     closure count.
  3. N=6 closure count distribution. The unique-non-classifier assumption
     fails (some shapes have multiple non-classifiers); generalize the
     closure-count notion: count triples (a, b, c) ∈ core³ with λ(b)
     core-preserving and λ(c) ∘ λ(b)|_core = λ(a)|_core.

  Bonus: count distinct R(X) partial-monoid iso types at N=5.

Outputs printed to stdout. Run from anywhere: paths are absolute.
"""

from __future__ import annotations

import itertools
import json
import os
from collections import Counter, defaultdict

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N5_DATA = os.path.join(SCRIPT_DIR, "phase_cartography_N5.json")
N6_DATA = os.path.join(SCRIPT_DIR, "phase_cartography_N6.json")


def core_of(N):
    return tuple(range(2, N))


def is_classifier_row(table, a, ABS=(0, 1), CORE=None):
    return all(table[a][x] in ABS for x in CORE)


def is_core_preserving(table, a, CORE):
    return all(table[a][x] in CORE for x in CORE)


def composition_closures(table, N):
    """Count triples (a, b, c) ∈ core³ with λ(b) core-preserving and
    λ(c) ∘ λ(b)|_core = λ(a)|_core. No distinctness constraint.
    Returns the list of triples."""
    CORE = core_of(N)
    out = []
    for b in CORE:
        if not is_core_preserving(table, b, CORE):
            continue
        for c in CORE:
            target = tuple(table[c][table[b][x]] for x in CORE)
            for a in CORE:
                if tuple(table[a][x] for x in CORE) == target:
                    out.append((a, b, c))
    return out


def closure_count(table, N):
    return len(composition_closures(table, N))


def apply_permutation(table, sigma):
    """Conjugate an N×N magma table by permutation sigma:
    new_table[sigma[a]][sigma[b]] = sigma[table[a][b]]."""
    N = len(table)
    new_table = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            new_table[sigma[a]][sigma[b]] = sigma[table[a][b]]
    return new_table


# ------------------------------------------------------------------
# Question 1: Iso-invariance under absorber-preserving permutations.
# ------------------------------------------------------------------

def absorber_preserving_perms(N):
    """Permutations of {0,...,N-1} fixing {0,1} as a set."""
    rest = list(range(2, N))
    out = []
    for fix in [(0, 1), (1, 0)]:  # action on absorber set
        for perm in itertools.permutations(rest):
            sigma = [0] * N
            sigma[0], sigma[1] = fix
            for i, x in enumerate(rest):
                sigma[x] = perm[i]
            out.append(sigma)
    return out


def test_iso_invariance(iso_classes, N, n_classes_to_check=20):
    print(f"=== Q1: closure-count iso-invariance under absorber-preserving permutations (N={N}) ===")
    perms = absorber_preserving_perms(N)
    print(f"  testing {n_classes_to_check} classes against {len(perms)} permutations each")
    n_invariant = 0
    n_violation = 0
    failing = []
    for c in iso_classes[:n_classes_to_check]:
        T = c["canonical"]
        base = closure_count(T, N)
        for sigma in perms:
            T2 = apply_permutation(T, sigma)
            cc2 = closure_count(T2, N)
            if cc2 != base:
                n_violation += 1
                failing.append((c["iso_class"], sigma, base, cc2))
                break
        else:
            n_invariant += 1
    print(f"  invariant: {n_invariant}/{n_classes_to_check}")
    if failing:
        print(f"  VIOLATIONS: {failing[:3]}")
    else:
        print("  OK: closure count invariant under absorber-preserving permutations across sample.")
    return n_invariant == n_classes_to_check


# ------------------------------------------------------------------
# Question 2: Structural characterization of the 2/4/5 split at N=5.
# ------------------------------------------------------------------

def classify_g_action(T, N=5):
    """For an N=5 S+D+C magma, find the unique non-classifier g in core
    and return its row restricted to core, plus classification:
      - 'identity' if (2,3,4)
      - 'involution_*' if non-identity self-inverse permutation on core
      - 'permutation' if other permutation on core
      - 'non_permutation' otherwise."""
    CORE = core_of(N)
    g = None
    for a in CORE:
        if is_core_preserving(T, a, CORE):
            g = a
            break
    if g is None:
        return ("none", None, None)
    row = tuple(T[g][x] for x in CORE)  # image under g of CORE
    # Identity row?
    is_id = all(T[g][x] == x for x in CORE)
    if is_id:
        return ("identity", g, row)
    # Permutation?
    if len(set(row)) == len(CORE):
        # Check involution: g(g(x)) = x for x in CORE
        is_invol = all(T[g][T[g][x]] == x for x in CORE)
        if is_invol:
            return ("involution", g, row)
        return ("non_invol_perm", g, row)
    return ("non_permutation", g, row)


def test_24_5_split(iso_classes):
    print()
    print("=== Q2: Structural characterization of 2/4/5 split at N=5 ===")
    cross = Counter()
    by_action = defaultdict(list)
    by_row = Counter()
    by_row_cc = defaultdict(Counter)
    for c in iso_classes:
        T = c["canonical"]
        action, g, row = classify_g_action(T)
        cc = closure_count(T, 5)
        cross[(action, cc)] += 1
        by_action[action].append((c["iso_class"], cc))
        by_row[row] += 1
        by_row_cc[row][cc] += 1
    print("  Cross-tab (g_action, closure_count) -> count:")
    for k, v in sorted(cross.items()):
        print(f"    {k}: {v}")
    print()
    print("  Distinct row patterns of g on core (image triple):")
    for r, n in sorted(by_row.items(), key=lambda kv: -kv[1]):
        cc_dist = dict(by_row_cc[r])
        print(f"    g|core = {r}: {n} classes; closure-count distribution = {cc_dist}")
    return cross, by_row_cc


# ------------------------------------------------------------------
# Question 3: N=6 closure-count distribution and per-shape breakdown.
# ------------------------------------------------------------------

def n6_analysis(iso_classes):
    print()
    print("=== Q3: N=6 closure-count distribution ===")
    cc_dist = Counter()
    shape_cc = defaultdict(Counter)
    for c in iso_classes:
        T = c["canonical"]
        cc = closure_count(T, 6)
        cc_dist[cc] += 1
        shape_cc[c["role_shape"]][cc] += 1
    print(f"  Overall closure-count distribution at N=6 ({len(iso_classes)} classes):")
    for k in sorted(cc_dist):
        print(f"    {k}: {cc_dist[k]}")
    print()
    print("  Per-role-shape closure-count distributions:")
    print(f"  {'role_shape':<35s} {'n_classes':>10s}  closure_count_dist")
    for shape in sorted(shape_cc):
        ccd = shape_cc[shape]
        n = sum(ccd.values())
        ccs = ", ".join(f"{k}:{v}" for k, v in sorted(ccd.items()))
        n_distinct_cc = len(ccd)
        marker = "  SPLIT" if n_distinct_cc > 1 else ""
        print(f"  {shape:<35s} {n:>10d}  {{{ccs}}}{marker}")
    return cc_dist, shape_cc


# ------------------------------------------------------------------
# Bonus: distinct R(X) partial-monoid iso types at N=5.
# ------------------------------------------------------------------

def partial_monoid_invariant_N5(T):
    """Build a canonical hashable signature of the row-image partial monoid
    of an N=5 magma. R(X) ⊆ X^X has 5 elements (rows of the magma table).
    Two magmas have isomorphic partial monoids if there is a bijection
    of their row sets preserving the partial-composition relation
    R = {(f, g, h) : g ∘ f = h, h ∈ R(X)}.

    We compute an invariant via Weisfeiler-Lehman style refinement on
    the 5 rows. Initial label: row's structural type
      ('abs', img-of-core), ('clas', img-of-core), ('core_pres', img-of-core)
    where the image is a multiset of role-labels.

    Then iteratively refine: each row's new label is its (old label,
    multiset of (other_old_label, comp_old_label)) over the partial
    composition table.
    """
    N = 5
    CORE = core_of(N)
    ABS = (0, 1)
    rows = [tuple(T[a]) for a in range(N)]

    # Role of each row.
    def init_label(a):
        # role categories
        if a in ABS:
            return ("abs",)
        # On core only, classify by where image of core lies
        img_core = tuple(T[a][x] for x in CORE)
        if all(y in ABS for y in img_core):
            return ("clas", tuple(sorted(img_core)))
        if all(y in CORE for y in img_core):
            # core-preserving: capture "shape" by frequency of values
            mset = tuple(sorted(Counter(img_core).values()))
            return ("core_pres", mset)
        return ("mixed", tuple(sorted(img_core)))

    labels = [init_label(a) for a in range(N)]

    def compose(a, b):
        """Compute λ(b) ∘ λ(a) as a row tuple."""
        return tuple(T[b][T[a][x]] for x in range(N))

    # Build composition relation: for each (a, b), if compose(a, b) is
    # equal to some row(c), record (a, b, c). Otherwise no partial comp.
    row_to_idx = defaultdict(list)
    for i, r in enumerate(rows):
        row_to_idx[r].append(i)

    comp_target = {}  # (a, b) -> c if defined
    for a in range(N):
        for b in range(N):
            r = compose(a, b)
            if r in row_to_idx:
                # By extensionality there should be a unique c (rows are distinct)
                cs = row_to_idx[r]
                # Pick any (rows are guaranteed distinct in extensional magmas)
                comp_target[(a, b)] = cs[0]

    # Refine labels via WL.
    for _ in range(N + 2):
        new_labels = []
        for a in range(N):
            edges_out = []
            for b in range(N):
                if (a, b) in comp_target:
                    edges_out.append(("R", labels[b], labels[comp_target[(a, b)]]))
                else:
                    edges_out.append(("R", labels[b], None))
                if (b, a) in comp_target:
                    edges_out.append(("L", labels[b], labels[comp_target[(b, a)]]))
                else:
                    edges_out.append(("L", labels[b], None))
            new_labels.append((labels[a], tuple(sorted(map(str, edges_out)))))
        # Canonicalize via stable sort -> mapping to small ids
        # but keep the structured tuple for next round
        if all(new_labels[i] == new_labels[j]
               for i in range(N) for j in range(N)
               if labels[i] == labels[j] and new_labels[i] != new_labels[j]):
            pass
        if new_labels == labels:
            break
        # compress
        seen = {}
        compressed = []
        for lab in new_labels:
            if lab not in seen:
                seen[lab] = len(seen)
            compressed.append(("v", seen[lab]))
        if compressed == labels:
            break
        labels = compressed

    # Now produce the partial-monoid signature: multiset of label
    # patterns plus the labelled composition table.
    signature_parts = []
    signature_parts.append(("labels_multiset", tuple(sorted(map(str, labels)))))
    # Labelled comp table
    edges = []
    for (a, b), c in comp_target.items():
        edges.append((str(labels[a]), str(labels[b]), str(labels[c])))
    signature_parts.append(("edges_multiset", tuple(sorted(edges))))
    # Existence pattern: which (la, lb) pairs have any composition target
    presence = set()
    for a in range(N):
        for b in range(N):
            presence.add((str(labels[a]), str(labels[b]), (a, b) in comp_target))
    signature_parts.append(("presence", tuple(sorted(map(str, presence)))))
    return tuple(signature_parts)


def bonus_partial_monoid_types(iso_classes):
    print()
    print("=== Bonus: distinct R(X) partial-monoid iso types (N=5, WL invariant) ===")
    types = Counter()
    type_to_examples = defaultdict(list)
    for c in iso_classes:
        T = c["canonical"]
        sig = partial_monoid_invariant_N5(T)
        types[sig] += 1
        if len(type_to_examples[sig]) < 1:
            type_to_examples[sig].append(c["iso_class"])
    print(f"  Distinct WL signatures (upper bound on iso types -> coarser when collisions): {len(types)}")
    print(f"  Top 10 signatures by frequency:")
    for sig, n in sorted(types.items(), key=lambda kv: -kv[1])[:10]:
        ex = type_to_examples[sig][0]
        print(f"    n={n}, example iso_class={ex}")
    print("  (WL is a lower bound on partial-monoid iso classes — different signatures imply different types,")
    print("   but two non-isomorphic partial monoids could in principle share a WL signature.)")
    return types


# ------------------------------------------------------------------

def main():
    print("Loading N=5 data...")
    with open(N5_DATA) as f:
        d5 = json.load(f)
    iso5 = d5["iso_classes"]

    print("Loading N=6 data...")
    with open(N6_DATA) as f:
        d6 = json.load(f)
    iso6 = d6["iso_classes"]

    test_iso_invariance(iso5, 5, n_classes_to_check=30)
    cross, by_row_cc = test_24_5_split(iso5)
    n6_analysis(iso6)
    bonus_partial_monoid_types(iso5)


if __name__ == "__main__":
    main()

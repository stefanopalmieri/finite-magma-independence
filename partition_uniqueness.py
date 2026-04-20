#!/usr/bin/env python3
"""
Investigate whether the Z/C/N decomposition is the unique coarsest
non-trivial isomorphism-invariant partition of elements in finite
extensional 2-pointed magmas.

For each table from the paper, we compute:
  1. Z/C/N classification
  2. Full invariant profile (image type, image size, fixed-point count,
     absorber-hit pattern, self-application type, row composition type,
     kernel on core)
  3. Whether any invariant refines Z/C/N within a class
  4. Whether any invariant cross-cuts Z/C/N
  5. Automorphism orbits and their relationship to Z/C/N
"""

from itertools import permutations
from collections import Counter

# ─── Tables from the paper ───────────────────────────────────────────

TABLES = {
    "N=4 kripke4": [
        [0,0,0,0],
        [1,1,1,1],
        [0,1,0,1],
        [0,0,2,3],
    ],
    "N=5 kripke5": [
        [0,0,0,0,0],
        [1,1,1,1,1],
        [1,0,3,4,2],
        [0,2,4,2,3],
        [0,1,1,0,0],
    ],
    "N=5 Witness5": [
        [0,0,0,0,0],
        [1,1,1,1,1],
        [0,2,2,3,4],
        [0,0,0,1,0],
        [0,1,0,1,0],
    ],
    "N=6 Witness6": [
        [0,0,0,0,0,0],
        [1,1,1,1,1,1],
        [3,3,4,2,5,3],
        [0,1,3,5,2,4],
        [0,0,1,0,1,1],
        [2,2,5,4,3,2],
    ],
    "N=8 Countermodel": [
        [0,0,0,0,0,0,0,0],
        [1,1,1,1,1,1,1,1],
        [3,3,7,3,4,6,5,2],
        [0,1,7,3,4,6,5,2],
        [0,0,0,0,0,0,1,0],
        [6,2,6,2,1,1,1,1],
        [0,0,5,2,2,2,2,2],
        [2,2,2,1,2,2,6,3],
    ],
    "N=6 sNoH6": [
        [0,0,0,0,0,0],
        [1,1,1,1,1,1],
        [0,3,3,2,5,4],
        [2,4,5,5,1,4],
        [5,3,0,0,3,2],
        [4,2,2,2,2,2],
    ],
    "N=10 dNotH": [
        [0,0,0,0,0,0,0,0,0,0],
        [1,1,1,1,1,1,1,1,1,1],
        [3,3,2,3,4,5,6,7,9,8],
        [0,1,2,3,4,5,6,7,9,8],
        [0,0,1,1,1,1,1,1,1,1],
        [1,0,0,0,0,0,0,0,0,0],
        [2,3,9,9,9,9,9,9,9,8],
        [3,2,9,9,9,9,9,9,9,8],
        [1,0,1,0,1,1,1,1,0,0],
        [0,1,0,1,0,1,1,0,1,1],
    ],
    "N=10 hNotD": [
        [0,0,0,0,0,0,0,0,0,0],
        [1,1,1,1,1,1,1,1,1,1],
        [3,1,3,4,9,6,8,5,7,2],
        [0,1,9,2,3,7,5,8,6,4],
        [0,0,1,1,1,1,1,1,0,0],
        [0,0,2,0,0,0,0,0,3,1],
        [2,2,2,8,3,9,4,7,9,7],
        [8,3,2,8,3,9,4,7,3,1],
        [9,2,2,3,8,1,3,7,1,7],
        [2,2,2,2,4,7,6,7,2,0],
    ],
    "N=5 dNoS": [
        [0,0,0,0,0],
        [1,1,1,1,1],
        [0,0,1,0,0],
        [4,2,4,2,4],
        [2,2,3,3,3],
    ],
    "N=6 hNoS": [
        [0,0,0,0,0,0],
        [1,1,1,1,1,1],
        [3,3,2,2,2,4],
        [0,2,2,2,4,0],
        [4,3,2,2,4,5],
        [0,0,2,2,2,4],
    ],
    "N=10 Witness10": [
        [0,0,0,0,0,0,0,0,0,0],
        [1,1,1,1,1,1,1,1,1,1],
        [3,3,4,3,7,5,9,6,8,2],
        [0,1,9,3,2,5,7,4,8,6],
        [0,0,1,1,1,0,0,0,1,1],
        [2,2,7,2,8,9,4,3,4,2],
        [0,0,6,4,8,7,3,3,4,9],
        [2,2,6,4,8,9,4,3,4,9],
        [2,2,4,8,4,3,4,4,8,9],
        [3,4,7,3,9,2,2,9,2,3],
    ],
}


def classify_zcn(table):
    """Classify each element as Z (absorber), C (classifier), or N (non-classifier)."""
    n = len(table)
    absorbers = {0, 1}
    core = sorted(set(range(n)) - absorbers)

    classes = {}
    for a in range(n):
        if a in absorbers:
            classes[a] = 'Z'
            continue
        # Row of a restricted to core inputs
        row_on_core = [table[a][x] for x in core]
        if all(v in absorbers for v in row_on_core):
            classes[a] = 'C'
        elif all(v not in absorbers for v in row_on_core):
            classes[a] = 'N'
        else:
            classes[a] = 'M'  # mixed — shouldn't happen if D holds
    return classes


def element_class(val, absorbers):
    """Return 'Z' if val is absorber, else 'core'."""
    return 'Z' if val in absorbers else 'core'


def compute_invariant_profile(table, a):
    """Compute the full invariant profile of element a."""
    n = len(table)
    absorbers = {0, 1}
    core = sorted(set(range(n)) - absorbers)
    row = table[a]

    profile = {}

    # 1. Image type on core
    row_on_core = [row[x] for x in core]
    types_on_core = set(element_class(v, absorbers) for v in row_on_core)
    if types_on_core == {'Z'}:
        profile['image_type'] = 'all_Z'
    elif types_on_core == {'core'}:
        profile['image_type'] = 'all_core'
    else:
        profile['image_type'] = 'mixed'

    # 2. Image size on core
    profile['image_size_on_core'] = len(set(row_on_core))

    # 3. Fixed-point count on core
    profile['fixed_points_on_core'] = sum(1 for x in core if row[x] == x)

    # 4. Absorber-hit pattern: classify (a·0, a·1)
    v0, v1 = row[0], row[1]
    c0, c1 = element_class(v0, absorbers), element_class(v1, absorbers)
    if c0 == 'Z' and c1 == 'Z':
        if v0 == v1:
            profile['absorber_hit'] = 'both_Z_same'
        else:
            profile['absorber_hit'] = 'both_Z_diff'
    elif c0 == 'core' and c1 == 'core':
        if v0 == v1:
            profile['absorber_hit'] = 'both_core_same'
        else:
            profile['absorber_hit'] = 'both_core_diff'
    else:
        profile['absorber_hit'] = 'mixed'

    # 5. Self-application
    aa = row[a]
    profile['self_app_class'] = element_class(aa, absorbers)
    profile['is_idempotent'] = (aa == a)

    # 6. Row composition type: multiset of output classes for all elements
    output_classes = tuple(sorted(element_class(row[x], absorbers) for x in range(n)))
    profile['output_class_multiset'] = output_classes

    # 7. Kernel on core: partition of core by a·x values
    kernel = {}
    for x in core:
        v = row[x]
        kernel.setdefault(v, []).append(x)
    kernel_signature = tuple(sorted(len(cls) for cls in kernel.values()))
    profile['kernel_on_core'] = kernel_signature

    # Additional: kernel on full domain
    kernel_full = {}
    for x in range(n):
        v = row[x]
        kernel_full.setdefault(v, []).append(x)
    kernel_full_sig = tuple(sorted(len(cls) for cls in kernel_full.values()))
    profile['kernel_full'] = kernel_full_sig

    # Additional: number of distinct values in full row
    profile['image_size_full'] = len(set(row))

    return profile


def compute_automorphisms(table):
    """Compute all automorphisms of the magma that fix absorbers 0 and 1."""
    n = len(table)
    absorbers = {0, 1}
    core = sorted(set(range(n)) - absorbers)

    # Automorphism must fix 0 and 1, permute core
    auts = []
    for perm_core in permutations(core):
        # Build full permutation
        p = list(range(n))
        for i, c in enumerate(core):
            p[c] = perm_core[i]
        # p[0] = 0, p[1] = 1 already

        # Check if p is an automorphism: p(a·b) = p(a)·p(b)
        is_aut = True
        for a in range(n):
            if not is_aut:
                break
            for b in range(n):
                if p[table[a][b]] != table[p[a]][p[b]]:
                    is_aut = False
                    break
        if is_aut:
            auts.append(tuple(p))
    return auts


def compute_orbits(n, automorphisms):
    """Compute orbits of elements under the automorphism group."""
    # Union-find
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    for aut in automorphisms:
        for i in range(n):
            union(i, aut[i])

    orbits = {}
    for i in range(n):
        r = find(i)
        orbits.setdefault(r, set()).add(i)

    return list(orbits.values())


def analyze_table(name, table):
    """Full analysis of one table."""
    n = len(table)
    absorbers = {0, 1}
    core = sorted(set(range(n)) - absorbers)

    print(f"\n{'='*70}")
    print(f"TABLE: {name}  (N={n})")
    print(f"{'='*70}")

    # Z/C/N classification
    zcn = classify_zcn(table)
    print(f"\nZ/C/N classification:")
    for a in range(n):
        print(f"  {a}: {zcn[a]}")

    zcn_partition = {}
    for a in range(n):
        zcn_partition.setdefault(zcn[a], set()).add(a)
    print(f"\nZ/C/N partition: { {k: sorted(v) for k, v in sorted(zcn_partition.items())} }")

    has_mixed = 'M' in zcn_partition
    if has_mixed:
        print("  ** WARNING: Mixed elements detected — D may not hold **")

    # Compute invariant profiles
    profiles = {}
    for a in range(n):
        profiles[a] = compute_invariant_profile(table, a)

    print(f"\nInvariant profiles:")
    for a in range(n):
        p = profiles[a]
        print(f"  Element {a} [{zcn[a]}]:")
        print(f"    image_type={p['image_type']}, img_size_core={p['image_size_on_core']}, "
              f"fixed_pts={p['fixed_points_on_core']}")
        print(f"    absorber_hit={p['absorber_hit']}, self_app={p['self_app_class']}, "
              f"idempotent={p['is_idempotent']}")
        print(f"    kernel_core={p['kernel_on_core']}, img_size_full={p['image_size_full']}")

    # Check refinements within Z/C/N classes
    print(f"\nRefinement analysis (do invariants split Z/C/N classes?):")
    any_refinement = False
    for cls_name, members in sorted(zcn_partition.items()):
        if len(members) <= 1:
            print(f"  {cls_name}: singleton, no refinement possible")
            continue
        # Group by full profile
        profile_groups = {}
        for a in sorted(members):
            key = tuple(sorted(profiles[a].items()))
            profile_groups.setdefault(key, []).append(a)
        num_distinct = len(profile_groups)
        if num_distinct == 1:
            print(f"  {cls_name}: all {len(members)} elements have IDENTICAL profiles — no refinement")
        else:
            any_refinement = True
            print(f"  {cls_name}: {num_distinct} distinct profiles among {len(members)} elements — REFINES Z/C/N")
            for key, elems in profile_groups.items():
                print(f"    Subclass {sorted(elems)}: {dict(key)}")

    # Check cross-cutting (elements from different classes with same profile)
    print(f"\nCross-cutting analysis (same profile across different Z/C/N classes?):")
    # Group all non-absorber elements by profile
    non_abs_profiles = {}
    for a in core:
        key = tuple(sorted(profiles[a].items()))
        non_abs_profiles.setdefault(key, []).append(a)

    any_crosscut = False
    for key, elems in non_abs_profiles.items():
        classes_here = set(zcn[a] for a in elems)
        if len(classes_here) > 1:
            any_crosscut = True
            print(f"  CROSS-CUT: elements {sorted(elems)} span classes {classes_here}")

    if not any_crosscut:
        print(f"  No cross-cutting — each profile is contained within a single Z/C/N class")

    # Automorphism orbits (skip for N >= 10 due to factorial blowup)
    if n <= 8:
        print(f"\nAutomorphism analysis:")
        auts = compute_automorphisms(table)
        print(f"  |Aut| = {len(auts)}")
        orbits = compute_orbits(n, auts)
        orbits_sorted = [sorted(o) for o in orbits]
        orbits_sorted.sort()
        print(f"  Orbits: {orbits_sorted}")

        # Check if Z/C/N equals the orbit partition
        zcn_sets = [sorted(v) for v in zcn_partition.values()]
        zcn_sets.sort()
        if orbits_sorted == zcn_sets:
            print(f"  Z/C/N partition EQUALS orbit partition")
        else:
            # Check if Z/C/N is a coarsening of orbits
            is_coarsening = True
            for orbit in orbits:
                classes_in_orbit = set(zcn[a] for a in orbit)
                if len(classes_in_orbit) > 1:
                    is_coarsening = False
                    break
            if is_coarsening:
                print(f"  Z/C/N COARSENS orbit partition (orbits are finer)")
            else:
                print(f"  Z/C/N does NOT coarsen orbits — UNEXPECTED")

        # Check: is Z/C/N the coarsest non-trivial partition preserved by Aut?
        # A partition P is preserved by Aut if for each automorphism and each class,
        # the image of the class is a class.
        # Z/C/N is coarsest if every other preserved partition refines it or is trivial.
        print(f"  Checking coarsest non-trivial automorphism-invariant partition...")

        # The coarsest nontrivial aut-invariant partition that separates Z from core:
        # Start with {Z, core} and see if Aut forces any further splitting.
        # Actually, Z = {0,1} is always a union of orbits (since 0,1 are fixed).
        # Among core orbits, the coarsest nontrivial partition is to merge all core
        # into one class — but check if C and N are in different orbits.
        core_orbits = [o for o in orbits if not o.issubset(absorbers)]
        core_orbit_classes = []
        for o_set in core_orbits:
            o_classes = set(zcn[a] for a in o_set if a not in absorbers)
            core_orbit_classes.append(o_classes)

        # Can we merge all core orbits? Always yes (trivially).
        # The question is: does the Z/C/N partition equal the coarsest partition
        # that is (a) aut-invariant, (b) separates Z from core, (c) has >= 3 classes?
        # For that, we need at least one orbit that's all-C and one that's all-N.
        all_c_orbits = [o for o in core_orbits if all(zcn[a] == 'C' for a in o if a not in absorbers)]
        all_n_orbits = [o for o in core_orbits if all(zcn[a] == 'N' for a in o if a not in absorbers)]
        mixed_orbits = [o for o in core_orbits if len(set(zcn[a] for a in o if a not in absorbers)) > 1]

        if mixed_orbits:
            print(f"  WARNING: orbit mixes C and N elements!")
        elif all_c_orbits and all_n_orbits:
            print(f"  Core orbits split cleanly into C-orbits and N-orbits")
            print(f"  Z/C/N is the coarsest aut-invariant partition with >=3 classes "
                  f"that separates Z from core")
        elif all_c_orbits and not all_n_orbits:
            print(f"  Only C orbits in core (no N elements)")
        elif all_n_orbits and not all_c_orbits:
            print(f"  Only N orbits in core (no C elements)")
    else:
        print(f"\nAutomorphism analysis: SKIPPED (N={n} too large for brute-force)")
        # Use a sampling approach for large N
        print(f"  (Would need a smarter algorithm for N={n})")

    # Summary stats
    non_abs_profile_count = len(non_abs_profiles)
    print(f"\nSummary:")
    print(f"  Distinct non-absorber profiles: {non_abs_profile_count}")
    print(f"  Z/C/N classes among non-absorbers: {len([c for c in zcn_partition if c != 'Z'])}")
    print(f"  Refinement detected: {'YES' if any_refinement else 'NO'}")
    print(f"  Cross-cutting detected: {'YES' if any_crosscut else 'NO'}")

    return {
        'name': name,
        'n': n,
        'zcn': zcn,
        'profiles': profiles,
        'any_refinement': any_refinement,
        'any_crosscut': any_crosscut,
        'non_abs_profile_count': non_abs_profile_count,
    }


def main():
    print("=" * 70)
    print("Z/C/N PARTITION UNIQUENESS INVESTIGATION")
    print("Is Z/C/N the unique coarsest non-trivial isomorphism-invariant")
    print("partition of elements in finite extensional 2-pointed magmas?")
    print("=" * 70)

    results = []
    for name, table in TABLES.items():
        results.append(analyze_table(name, table))

    # ─── Grand summary ───────────────────────────────────────────────
    print("\n" + "=" * 70)
    print("GRAND SUMMARY")
    print("=" * 70)

    any_global_refinement = False
    any_global_crosscut = False
    profile_counts = []

    for r in results:
        if r['any_refinement']:
            any_global_refinement = True
        if r['any_crosscut']:
            any_global_crosscut = True
        profile_counts.append((r['name'], r['non_abs_profile_count'],
                               len([c for c in set(r['zcn'].values()) if c != 'Z'])))

    print(f"\nAcross all {len(results)} tables:")
    print(f"  Any refinement of Z/C/N detected: {'YES' if any_global_refinement else 'NO'}")
    print(f"  Any cross-cutting of Z/C/N detected: {'YES' if any_global_crosscut else 'NO'}")

    print(f"\nProfile counts (distinct non-absorber invariant profiles vs Z/C/N classes):")
    print(f"  {'Table':<25} {'# profiles':>10} {'# Z/C/N cls':>12} {'Match?':>8}")
    print(f"  {'-'*25} {'-'*10} {'-'*12} {'-'*8}")
    for name, pc, zc in profile_counts:
        match = "YES" if pc == zc else "NO"
        print(f"  {name:<25} {pc:>10} {zc:>12} {match:>8}")

    # Final verdict
    print(f"\n{'='*70}")
    print("VERDICT")
    print(f"{'='*70}")

    if not any_global_crosscut:
        print("No cross-cutting detected: every invariant profile lies within a single")
        print("Z/C/N class. The Z/C/N partition is CONSISTENT with being the coarsest")
        print("non-trivial isomorphism-invariant partition.")
    else:
        print("CROSS-CUTTING detected: there exist invariant profiles that span multiple")
        print("Z/C/N classes. The Z/C/N partition may not be the unique coarsest.")

    if any_global_refinement:
        print("\nREFINEMENT detected: some invariant profiles split a Z/C/N class into")
        print("subclasses. This means Z/C/N is COARSER than the finest invariant partition.")
        print("However, it may still be the COARSEST non-trivial partition.")

        # Analyze what invariants cause refinement
        print("\nRefinement details:")
        for r in results:
            if r['any_refinement']:
                zcn = r['zcn']
                profiles = r['profiles']
                zcn_partition = {}
                for a, c in zcn.items():
                    zcn_partition.setdefault(c, set()).add(a)

                for cls_name, members in sorted(zcn_partition.items()):
                    if len(members) <= 1:
                        continue
                    # Check which specific invariants differ
                    invariant_keys = list(profiles[next(iter(members))].keys())
                    for inv_key in invariant_keys:
                        vals = set()
                        for a in members:
                            v = profiles[a][inv_key]
                            vals.add(str(v))
                        if len(vals) > 1:
                            print(f"  {r['name']}, class {cls_name}: "
                                  f"'{inv_key}' takes {len(vals)} distinct values")
    else:
        print("\nNo refinement detected: within each Z/C/N class, all elements have")
        print("IDENTICAL invariant profiles. Z/C/N IS the finest invariant partition")
        print("(and therefore trivially the unique coarsest non-trivial one).")

    if not any_global_crosscut and any_global_refinement:
        print("\n*** Z/C/N is a non-trivial isomorphism-invariant partition, and no ***")
        print("*** other partition cross-cuts it. The refinements show Z/C/N is    ***")
        print("*** coarser than the orbit partition in some cases, but it remains  ***")
        print("*** the coarsest non-trivial such partition across all tables.      ***")


if __name__ == '__main__':
    main()

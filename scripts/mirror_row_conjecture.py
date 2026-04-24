"""
Test the mirror-row conjecture for N=5 non-rigidity.

Conjecture (from scripts/PHASE_CARTOGRAPHY_FINDINGS.md §1):

  An S+D+C magma at N=5 is non-rigid (|Aut| ≥ 2) iff its two full
  classifiers τ1, τ2 admit a core-permutation σ such that σ is an
  automorphism of the Cayley table and σ(τ1) = τ2.

This script walks every sampled iso class from phase_cartography_N5.json
and tabulates:

  (# full classifiers, ∃ classifier-swap automorphism) × rigid?

Expected from the cartography data:
  - Exactly 12 non-rigid classes, all with 2 full classifiers.
  - If the conjecture holds: every non-rigid class has some classifier-
    swap automorphism, and no rigid 2-full-classifier class does.
"""

from __future__ import annotations

import itertools
import json
import os

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N = 5
CORE = (2, 3, 4)


def is_homomorphism(table, sigma):
    return all(sigma[table[a][b]] == table[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N))


def classifier_swap_aut_exists(table, full_cls):
    """∃ a core-permutation σ (absorber-fixing) with σ(τ1) = τ2, σ(τ2) = τ1,
    and σ an automorphism of the whole table?"""
    if len(full_cls) != 2:
        return False
    tau1, tau2 = full_cls
    core_list = list(CORE)
    for core_perm in itertools.permutations(core_list):
        sigma = [0, 1] + list(core_perm)
        if sigma[tau1] != tau2:
            continue
        if sigma[tau2] != tau1:
            continue
        if is_homomorphism(table, sigma):
            return True
    return False


def full_classifiers(table):
    return [y for y in CORE if all(table[y][x] in (0, 1) for x in range(N))]


def main():
    with open(os.path.join(SCRIPT_DIR, "phase_cartography_N5.json")) as f:
        d = json.load(f)

    buckets = {(fc, has_swap, rigid): 0
               for fc in (0, 1, 2)
               for has_swap in (False, True)
               for rigid in (False, True)}

    non_rigid_records = []

    for c in d["iso_classes"]:
        table = c["canonical"]
        fc = full_classifiers(table)
        has_swap = classifier_swap_aut_exists(table, fc)
        rigid = c["rigid"]
        buckets[(len(fc), has_swap, rigid)] += 1

        if not rigid:
            non_rigid_records.append((c["iso_class"], len(fc), has_swap, c["aut_order"]))

    print("Phase-cartography N=5 / Mirror-row conjecture test")
    print("=" * 56)
    print()
    print("Cells: (#full classifiers, classifier-swap aut, rigid) → count")
    for k in sorted(buckets.keys()):
        if buckets[k]:
            fc, swap, rigid = k
            print(f"  full_cls={fc}, swap_aut={str(swap):5}, "
                  f"rigid={str(rigid):5} → {buckets[k]}")
    print()

    print("Non-rigid classes (id, #full_cls, has_swap_aut, |Aut|):")
    for r in non_rigid_records:
        print(f"  {r}")
    print()

    # Interpretation
    nr_with_swap = sum(1 for _, fc, s, _ in non_rigid_records if s)
    nr_total = len(non_rigid_records)
    rigid_2fc_with_swap = buckets[(2, True, True)]
    rigid_2fc_total = buckets[(2, False, True)] + buckets[(2, True, True)]

    print("Interpretation:")
    print(f"  Non-rigid → classifier-swap aut: {nr_with_swap}/{nr_total}")
    print(f"  Rigid & 2 full cls & classifier-swap aut: "
          f"{rigid_2fc_with_swap}/{rigid_2fc_total}")
    if nr_with_swap == nr_total and rigid_2fc_with_swap == 0:
        print("  ⇒ Conjecture holds on this sample: classifier-swap aut "
              "exists iff non-rigid.")
    else:
        print("  ⇒ Conjecture needs refinement.")


if __name__ == "__main__":
    main()

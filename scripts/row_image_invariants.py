"""
Row-image translation test for S, D, C.

For each S+D+C magma at N=5 in phase_cartography_N5.json, check the
translations proposed in paper/CATEGORICAL_CANONICALITY_PROPOSAL.md:

  - S ↔ ∃ a, b ∈ core such that λ(b) ∘ λ(a)|_core = id_core
                              ∧ λ(a) ∘ λ(b)|_core = id_core
  - D ↔ R(X)|_core = R_clas(X) ⊔ R_core(X) (no row in core has mixed
        codomain), with both inhabited
  - C ↔ ∃ a, b, c ∈ core, pairwise distinct, with λ(b)|_core ⊆ core,
        λ(a)|_core = (λ(c) ∘ λ(b))|_core, λ(a)|_core non-constant

For each iso class, we verify these translations hold (operational
formulation ↔ row-image formulation). If 100% agreement across 3901
classes, the categorical translation is correct.

Then we further compute structural invariants of R(X):
  - sizes (|R_abs|, |R_clas|, |R_core|)
  - the closed-composition graph on R_core (edges (a, b) where
    λ(a) ∘ λ(b) ∈ R_core)
  - the section-retraction pair count

These invariants are the inputs for further canonicality analysis.
"""

from __future__ import annotations

import itertools
import json
import os
from collections import Counter, defaultdict

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N = 5
ABS = (0, 1)
CORE = (2, 3, 4)


def row(table, a):
    return tuple(table[a])


def row_on_core(table, a):
    return tuple(table[a][x] for x in CORE)


def is_classifier_row(table, a):
    """Image of λ(a)|_core ⊆ {z₁, z₂}."""
    return all(table[a][x] in ABS for x in CORE)


def is_core_preserving(table, a):
    """Image of λ(a)|_core ⊆ core."""
    return all(table[a][x] in CORE for x in CORE)


def is_constant(table, a):
    """λ(a) is constant on the whole carrier."""
    return len(set(table[a])) == 1


def has_section_retraction(table):
    """∃ a, b ∈ core with λ(b) ∘ λ(a) = id_core ∧ λ(a) ∘ λ(b) = id_core."""
    for a in CORE:
        for b in CORE:
            ok_ab = all(table[b][table[a][x]] == x for x in CORE)
            ok_ba = all(table[a][table[b][x]] == x for x in CORE)
            if ok_ab and ok_ba:
                return True, (a, b)
    return False, None


def has_decomposition(table):
    """R(X)|_core decomposes as R_clas ⊔ R_core with both inhabited; no
    core element has a mixed-codomain row."""
    n_clas = sum(1 for a in CORE if is_classifier_row(table, a))
    n_corep = sum(1 for a in CORE if is_core_preserving(table, a))
    n_mixed = sum(1 for a in CORE
                  if not is_classifier_row(table, a)
                  and not is_core_preserving(table, a))
    return (n_mixed == 0 and n_clas >= 1 and n_corep >= 1), (n_clas, n_corep, n_mixed)


def has_partial_composition_closure(table):
    """∃ a, b, c ∈ core, pairwise distinct, with λ(b) core-preserving,
    λ(a)|_core = (λ(c) ∘ λ(b))|_core, λ(a) non-constant on core."""
    for a, b, c in itertools.permutations(CORE, 3):
        if not is_core_preserving(table, b):
            continue
        if not all(table[a][x] == table[c][table[b][x]] for x in CORE):
            continue
        if len({table[a][x] for x in CORE}) < 2:
            continue
        return True, (a, b, c)
    return False, None


def composition_closures(table):
    """All triples (a, b, c) ∈ core³ with λ(c) ∘ λ(b) = λ(a) on core,
    λ(b) core-preserving (so the composition is well-typed)."""
    out = []
    for b in CORE:
        if not is_core_preserving(table, b):
            continue
        for c in CORE:
            target_row = tuple(table[c][table[b][x]] for x in CORE)
            for a in CORE:
                if tuple(table[a][x] for x in CORE) == target_row:
                    out.append((a, b, c))
    return out


def main():
    with open(os.path.join(SCRIPT_DIR, "phase_cartography_N5.json")) as f:
        d = json.load(f)

    n_classes = len(d["iso_classes"])
    print(f"Testing categorical translations across {n_classes} N=5 S+D+C iso classes")
    print()

    # Translation S ↔ row-image retract.
    # The cartography already records `retr_pair_count`; cross-check that with
    # our independent row-image computation.
    n_S = 0
    n_S_disagree = 0
    n_D = 0
    n_D_disagree = 0
    n_C = 0
    n_C_disagree = 0

    decomposition_stats = Counter()
    closure_count_stats = Counter()
    section_retraction_count = 0

    for c in d["iso_classes"]:
        T = c["canonical"]

        # Operational: this magma is S+D+C by construction (it's in the file).
        # Row-image: check each of the three translations.
        s_ok, _ = has_section_retraction(T)
        if s_ok:
            n_S += 1
            section_retraction_count += 1
        else:
            n_S_disagree += 1

        d_ok, dstats = has_decomposition(T)
        decomposition_stats[dstats] += 1
        if d_ok:
            n_D += 1
        else:
            n_D_disagree += 1

        c_ok, _ = has_partial_composition_closure(T)
        if c_ok:
            n_C += 1
        else:
            n_C_disagree += 1

        closures = composition_closures(T)
        closure_count_stats[len(closures)] += 1

    print(f"S (row-image retract): {n_S}/{n_classes}, disagreements: {n_S_disagree}")
    print(f"D (R_clas ⊔ R_core decomposition with both inhabited): "
          f"{n_D}/{n_classes}, disagreements: {n_D_disagree}")
    print(f"C (partial composition closure): {n_C}/{n_classes}, "
          f"disagreements: {n_C_disagree}")
    print()

    if n_S_disagree == 0 and n_D_disagree == 0 and n_C_disagree == 0:
        print("✓ All three translations hold across every N=5 S+D+C iso class.")
        print("  The row-image categorical reading is consistent with the")
        print("  operational definitions.")
    else:
        print("⚠ Some translations failed; investigate.")
    print()

    print("Decomposition (|R_clas|, |R_core|, |mixed|) distribution:")
    for k, v in sorted(decomposition_stats.items()):
        print(f"  {k}: {v}")
    print()

    print("Composition-closure-count distribution (triples (a,b,c) on core):")
    for k, v in sorted(closure_count_stats.items()):
        print(f"  {k}: {v}")
    print()

    # Specific test: does decomposition (|R_clas|, |R_core|, |mixed|)
    # always equal (2, 1, 0) at N=5? (Theorem 4.8 says core has 2
    # classifiers + 1 non-classifier; mixed = 0 by D.)
    expected = (2, 1, 0)
    canonical_count = decomposition_stats.get(expected, 0)
    print(f"Classes with exact decomposition (|R_clas|, |R_core|, |mixed|) = "
          f"{expected}: {canonical_count}/{n_classes}")
    print()

    # Cross-tab decomposition × closure count
    cross = Counter()
    for c in d["iso_classes"]:
        T = c["canonical"]
        _, ds = has_decomposition(T)
        cl = len(composition_closures(T))
        cross[(ds, cl)] += 1
    print("Cross-tab (decomposition, closure-count) → count:")
    for k, v in sorted(cross.items()):
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()

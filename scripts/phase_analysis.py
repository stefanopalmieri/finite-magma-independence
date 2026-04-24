"""
Cross-N analysis of phase_cartography_N<N>.json outputs.

Loads all phase_cartography_N*.json files in the scripts/ directory and
produces a comparison table of role-shape distributions and rigidity
statistics across N. Looks for evidence of sub-transitions beyond the
known N=5 → N=6 transition.

Usage:
    python3 phase_analysis.py
"""

from __future__ import annotations

import glob
import json
import os
import sys
from collections import Counter

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def load_all():
    data = {}
    for path in sorted(glob.glob(os.path.join(SCRIPT_DIR,
                                              "phase_cartography_N*.json"))):
        with open(path) as f:
            d = json.load(f)
        data[d["N"]] = d
    return data


def percent(n, total):
    return f"{100 * n / total:.1f}%" if total else "n/a"


def print_table(rows, headers):
    widths = [max(len(str(r[i])) for r in rows + [headers]) for i in range(len(headers))]
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    print(fmt.format(*headers))
    print(fmt.format(*["-" * w for w in widths]))
    for r in rows:
        print(fmt.format(*[str(x) for x in r]))


def main():
    data = load_all()
    if not data:
        print("No phase_cartography_N*.json files found. Run phase_cartography.py first.")
        sys.exit(1)

    print("=" * 72)
    print("Phase-transition cartography: cross-N summary")
    print("=" * 72)
    print()

    # Top-line table.
    rows = []
    for N in sorted(data.keys()):
        d = data[N]
        s = d["summary"]
        rows.append([
            N,
            s["iso_class_count"],
            f"{s['rigid_fraction']:.3f}",
            f"{s['strong_R_fraction']:.3f}",
            f"{d['elapsed_seconds']:.1f}s",
        ])
    print_table(rows, ["N", "iso_classes", "rigid_frac", "strongR_frac", "time"])
    print()

    # |Aut| distribution per N.
    print("Automorphism group order distribution:")
    for N in sorted(data.keys()):
        s = data[N]["summary"]
        print(f"  N={N}: " + ", ".join(f"|Aut|={k}→{v}"
                                         for k, v in s["aut_order_distribution"].items()))
    print()

    # Role-shape distribution per N — look for multiple shapes.
    print("Role-shape (cls_count, noncls_count, retr_pairs, H_triples, strongR) distribution:")
    for N in sorted(data.keys()):
        s = data[N]["summary"]
        shapes = s.get("role_shape_distribution", {})
        n_shapes = len(shapes)
        top = sorted(shapes.items(), key=lambda kv: -kv[1])[:8]
        print(f"  N={N}: {n_shapes} distinct shape(s)")
        for k, v in top:
            total = s["iso_class_count"]
            print(f"    {k}  →  {v}  ({percent(v, total)})")
    print()

    # Structure theorem checks: at any N, does the 'canonical' shape
    # (cls2_ncl1_Rp1_H2_sR0) still dominate? Does a new shape appear at N=6?
    print("Structure-theorem shape (cls2_ncl1_Rp1_H2_sR0) prevalence by N:")
    for N in sorted(data.keys()):
        s = data[N]["summary"]
        shapes = s.get("role_shape_distribution", {})
        canonical = "cls2_ncl1_Rp1_H2_sR0"
        total = s["iso_class_count"]
        n = shapes.get(canonical, 0)
        print(f"  N={N}: {n}/{total} = {percent(n, total)}")
    print()

    # Cross-tab: rigidity vs full_classifier_count per N.
    print("Rigidity × full_classifier_count cross-tabulation:")
    for N in sorted(data.keys()):
        d = data[N]
        ct = Counter()
        for c in d["iso_classes"]:
            ct[(c["rigid"], c["full_cls_count"])] += 1
        print(f"  N={N}: ", dict(ct))
    print()

    # Non-rigid sub-shape analysis.
    print("Non-rigid classes: sub-shape breakdown:")
    for N in sorted(data.keys()):
        d = data[N]
        nr = [c for c in d["iso_classes"] if not c["rigid"]]
        if not nr:
            print(f"  N={N}: 0 non-rigid classes.")
            continue
        shapes = Counter(c["role_shape"] for c in nr)
        auts = Counter(c["aut_order"] for c in nr)
        print(f"  N={N}: {len(nr)} non-rigid classes")
        print(f"    |Aut| distribution: {dict(auts)}")
        print(f"    role shapes:        {dict(shapes)}")
    print()

    # Emergent phase-transition signatures: what changes between
    # consecutive Ns?
    print("Changes between consecutive N (diff of shape distributions):")
    Ns = sorted(data.keys())
    for i in range(len(Ns) - 1):
        N1, N2 = Ns[i], Ns[i + 1]
        s1 = set(data[N1]["summary"].get("role_shape_distribution", {}).keys())
        s2 = set(data[N2]["summary"].get("role_shape_distribution", {}).keys())
        new_shapes = s2 - s1
        gone_shapes = s1 - s2
        print(f"  N={N1} → N={N2}:")
        if new_shapes:
            print(f"    + new shapes: {sorted(new_shapes)}")
        if gone_shapes:
            print(f"    - shapes disappearing: {sorted(gone_shapes)}")
        if not new_shapes and not gone_shapes:
            print("    (same shape set)")
    print()


if __name__ == "__main__":
    main()

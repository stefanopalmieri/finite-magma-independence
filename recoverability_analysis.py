#!/usr/bin/env python3
"""
Recoverability analysis for all Cayley tables in the LICS paper.

rec_L(table) = minimum k such that k columns jointly distinguish all rows.
rec_R(table) = minimum k such that k rows jointly distinguish all columns.
"""

from itertools import combinations

# ── Table definitions ──────────────────────────────────────────────────────

TABLES = {
    "N=4 minimal R+D (kripke4)": {
        "table": [
            [0,0,0,0],
            [1,1,1,1],
            [0,1,0,1],
            [0,0,2,3],
        ],
        "properties": "R+D",
        "notes": "CatKripkeWallMinimal.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "s (retract)", 3: "r (section)"},
        "tau": None,  # no separate classifier
        "s": 2, "r": 3,
    },
    "N=5 minimal R+D, s≠r (kripke5)": {
        "table": [
            [0,0,0,0,0],
            [1,1,1,1,1],
            [1,0,3,4,2],
            [0,2,4,2,3],
            [0,1,1,0,0],
        ],
        "properties": "R+D",
        "notes": "CatKripkeWallMinimal.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "s", 3: "r", 4: "inert/extra"},
        "tau": None, "s": 2, "r": 3,
    },
    "N=5 R+D+H (Witness5)": {
        "table": [
            [0,0,0,0,0],
            [1,1,1,1,1],
            [0,2,2,3,4],
            [0,0,0,1,0],
            [0,1,0,1,0],
        ],
        "properties": "R+D+H",
        "notes": "Witness5.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "classifier(τ)", 3: "s", 4: "r"},
        "tau": 2, "s": 3, "r": 4,
    },
    "N=6 R+D+H (Witness6)": {
        "table": [
            [0,0,0,0,0,0],
            [1,1,1,1,1,1],
            [3,3,4,2,5,3],
            [0,1,3,5,2,4],
            [0,0,1,0,1,1],
            [2,2,5,4,3,2],
        ],
        "properties": "R+D+H",
        "notes": "Witness6.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "classifier(τ)", 3: "s", 4: "inert", 5: "r"},
        "tau": 2, "s": 3, "r": 5,
    },
    "N=8 R-not-D (Countermodel)": {
        "table": [
            [0,0,0,0,0,0,0,0],
            [1,1,1,1,1,1,1,1],
            [3,3,7,3,4,6,5,2],
            [0,1,7,3,4,6,5,2],
            [0,0,0,0,0,0,1,0],
            [6,2,6,2,1,1,1,1],
            [0,0,5,2,2,2,2,2],
            [2,2,2,1,2,2,6,3],
        ],
        "properties": "R (no D)",
        "notes": "Countermodel.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "s", 3: "r", 4: "inert?", 5: "?", 6: "?", 7: "?"},
        "tau": None, "s": 2, "r": 3,
    },
    "N=6 R-not-H (sNoH6)": {
        "table": [
            [0,0,0,0,0,0],
            [1,1,1,1,1,1],
            [0,3,3,2,5,4],
            [2,4,5,5,1,4],
            [5,3,0,0,3,2],
            [4,2,2,2,2,2],
        ],
        "properties": "R (no H)",
        "notes": "E2PM.lean, sNoH6",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "s", 3: "r", 4: "?", 5: "?"},
        "tau": None, "s": 2, "r": 3,
    },
    "N=10 D-not-H (dNotH)": {
        "table": [
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
        "properties": "D (no H)",
        "notes": "Countermodels10.lean, dNotH",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "classifier(τ)", 3: "r", 4: "?", 5: "?",
                  6: "?", 7: "?", 8: "?", 9: "?"},
        "tau": 2, "s": None, "r": 3,
    },
    "N=10 H-not-D (hNotD)": {
        "table": [
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
        "properties": "H (no D)",
        "notes": "Countermodels10.lean, hNotD",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "s", 3: "r", 4: "?", 5: "?",
                  6: "?", 7: "?", 8: "?", 9: "?"},
        "tau": None, "s": 2, "r": 3,
    },
    "N=5 D-not-R (dNoS)": {
        "table": [
            [0,0,0,0,0],
            [1,1,1,1,1],
            [0,0,1,0,0],
            [4,2,4,2,4],
            [2,2,3,3,3],
        ],
        "properties": "D (no R)",
        "notes": "E2PM.lean, dNoS",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "classifier(τ)", 3: "?", 4: "?"},
        "tau": 2, "s": None, "r": None,
    },
    "N=6 H-not-R (hNoS)": {
        "table": [
            [0,0,0,0,0,0],
            [1,1,1,1,1,1],
            [3,3,2,2,2,4],
            [0,2,2,2,4,0],
            [4,3,2,2,4,5],
            [0,0,2,2,2,4],
        ],
        "properties": "H (no R)",
        "notes": "E2PM.lean, hNoS",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "?", 3: "?", 4: "?", 5: "?"},
        "tau": None, "s": None, "r": None,
    },
    "N=10 R+D+H separated (Witness10)": {
        "table": [
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
        "properties": "R+D+H",
        "notes": "Witness10.lean",
        "roles": {0: "absorber(⊤)", 1: "absorber(⊥)", 2: "classifier(τ)", 3: "s", 4: "inert",
                  5: "?", 6: "?", 7: "?", 8: "?", 9: "r"},
        "tau": 2, "s": 3, "r": 9,
    },
}


# ── Core functions ─────────────────────────────────────────────────────────

def columns_separate(table, col_indices):
    """Check if the given column indices jointly distinguish all rows."""
    N = len(table)
    tuples = set()
    for i in range(N):
        t = tuple(table[i][c] for c in col_indices)
        if t in tuples:
            return False
        tuples.add(t)
    return True


def rows_separate(table, row_indices):
    """Check if the given row indices jointly distinguish all columns."""
    N = len(table[0])
    tuples = set()
    for j in range(N):
        t = tuple(table[r][j] for r in row_indices)
        if t in tuples:
            return False
        tuples.add(t)
    return True


def rec_L(table):
    """Minimum k columns that jointly distinguish all rows. Returns (k, first optimal set)."""
    N = len(table)
    cols = list(range(N))
    for k in range(1, N + 1):
        for subset in combinations(cols, k):
            if columns_separate(table, subset):
                return k, list(subset)
    return N, cols  # fallback: all columns


def rec_R(table):
    """Minimum k rows that jointly distinguish all columns. Returns (k, first optimal set)."""
    N = len(table)
    rows = list(range(N))
    for k in range(1, N + 1):
        for subset in combinations(rows, k):
            if rows_separate(table, subset):
                return k, list(subset)
    return N, rows


def all_optimal_sets_L(table, k):
    """Return ALL k-subsets of columns that separate all rows."""
    N = len(table)
    return [list(s) for s in combinations(range(N), k) if columns_separate(table, s)]


# ── Targeted probing checks ───────────────────────────────────────────────

def check_probing(table, col_indices, label):
    """Check if specific columns separate all rows."""
    valid = [c for c in col_indices if c is not None and c < len(table)]
    if not valid:
        return f"{label}: N/A"
    sep = columns_separate(table, valid)
    return f"{label} (cols {valid}): {'YES' if sep else 'NO'}"


# ── Main analysis ──────────────────────────────────────────────────────────

def main():
    print("=" * 90)
    print("RECOVERABILITY ANALYSIS FOR LICS PAPER CAYLEY TABLES")
    print("=" * 90)
    print()

    results = []

    for name, info in TABLES.items():
        table = info["table"]
        N = len(table)

        kL, optL = rec_L(table)
        kR, optR = rec_R(table)

        # Get all optimal column sets
        all_opt = all_optimal_sets_L(table, kL)

        # Role labels for optimal columns
        roles = info.get("roles", {})
        opt_roles = [roles.get(c, "?") for c in optL]

        results.append({
            "name": name,
            "N": N,
            "properties": info["properties"],
            "rec_L": kL,
            "rec_R": kR,
            "opt_cols": optL,
            "opt_roles": opt_roles,
            "all_opt_count": len(all_opt),
            "all_opt": all_opt,
        })

        print(f"┌─ {name}")
        print(f"│  N = {N},  Properties: {info['properties']}")
        print(f"│  Source: {info['notes']}")
        print(f"│")
        print(f"│  rec_L = {kL}   (optimal cols: {optL})")
        print(f"│    roles: {opt_roles}")
        print(f"│    all optimal {kL}-col sets ({len(all_opt)} total): ", end="")
        if len(all_opt) <= 10:
            print(all_opt)
        else:
            print(f"{all_opt[:5]} ... ({len(all_opt)} total)")
        print(f"│  rec_R = {kR}   (optimal rows: {optR})")
        print(f"│")

        # Targeted probing checks
        tau = info.get("tau")
        s = info.get("s")
        r = info.get("r")

        print(f"│  Probing checks:")
        # Absorber column {0}
        print(f"│    {check_probing(table, [0], 'absorber {0}')}")
        # Classifier column {τ}
        if tau is not None:
            print(f"│    {check_probing(table, [tau], 'classifier {τ}')}")
        # Retraction pair {s, r}
        if s is not None and r is not None:
            print(f"│    {check_probing(table, [s, r], '{s,r} retraction pair')}")
        # Full {τ, s, r}
        if tau is not None and s is not None and r is not None:
            probes = sorted(set([tau, s, r]))
            print(f"│    {check_probing(table, probes, '{τ,s,r}')}")

        print(f"└{'─' * 88}")
        print()

    # ── Summary table ──────────────────────────────────────────────────────
    print()
    print("=" * 90)
    print("SUMMARY TABLE")
    print("=" * 90)
    print()
    header = f"{'Table':<42} {'N':>2} {'Props':<10} {'rec_L':>5} {'rec_R':>5} {'Opt cols':<20}"
    print(header)
    print("-" * len(header))
    for r in results:
        print(f"{r['name']:<42} {r['N']:>2} {r['properties']:<10} {r['rec_L']:>5} {r['rec_R']:>5} {str(r['opt_cols']):<20}")

    # ── Analysis of patterns ───────────────────────────────────────────────
    print()
    print("=" * 90)
    print("PATTERN ANALYSIS")
    print("=" * 90)
    print()

    # Group by properties
    props_map = {}
    for r in results:
        p = r["properties"]
        props_map.setdefault(p, []).append(r)

    print("rec_L by property combination:")
    print("-" * 50)
    for p, rs in sorted(props_map.items()):
        vals = [f"{r['name'].split('(')[0].strip()}: {r['rec_L']}" for r in rs]
        print(f"  {p:<12} -> {', '.join(vals)}")

    print()
    print("rec_L / N ratio (lower = more recoverable):")
    print("-" * 60)
    for r in sorted(results, key=lambda x: x["rec_L"] / x["N"]):
        ratio = r["rec_L"] / r["N"]
        bar = "█" * int(ratio * 40)
        print(f"  {r['name']:<42} {r['rec_L']}/{r['N']} = {ratio:.2f}  {bar}")

    print()
    print("Key observations:")
    print("-" * 60)

    # Check: does D imply lower rec_L?
    d_tables = [r for r in results if "D" in r["properties"]]
    no_d = [r for r in results if "D" not in r["properties"]]
    if d_tables and no_d:
        avg_d = sum(r["rec_L"]/r["N"] for r in d_tables) / len(d_tables)
        avg_no = sum(r["rec_L"]/r["N"] for r in no_d) / len(no_d)
        print(f"  Avg rec_L/N with D:    {avg_d:.3f}  (n={len(d_tables)})")
        print(f"  Avg rec_L/N without D: {avg_no:.3f}  (n={len(no_d)})")

    r_tables = [r for r in results if "R" in r["properties"]]
    no_r = [r for r in results if "R" not in r["properties"]]
    if r_tables and no_r:
        avg_r = sum(r["rec_L"]/r["N"] for r in r_tables) / len(r_tables)
        avg_no = sum(r["rec_L"]/r["N"] for r in no_r) / len(no_r)
        print(f"  Avg rec_L/N with R:    {avg_r:.3f}  (n={len(r_tables)})")
        print(f"  Avg rec_L/N without R: {avg_no:.3f}  (n={len(no_r)})")

    h_tables = [r for r in results if "H" in r["properties"]]
    no_h = [r for r in results if "H" not in r["properties"]]
    if h_tables and no_h:
        avg_h = sum(r["rec_L"]/r["N"] for r in h_tables) / len(h_tables)
        avg_no = sum(r["rec_L"]/r["N"] for r in no_h) / len(no_h)
        print(f"  Avg rec_L/N with H:    {avg_h:.3f}  (n={len(h_tables)})")
        print(f"  Avg rec_L/N without H: {avg_no:.3f}  (n={len(no_h)})")

    # Check: does absorber column alone ever suffice?
    print()
    print("Does probing col 0 (absorber) alone suffice?")
    for r in results:
        table = TABLES[r["name"]]["table"]
        yes = columns_separate(table, [0])
        print(f"  {r['name']:<42} {'YES' if yes else 'NO'}")

    # Check: does classifier alone suffice for D-tables?
    print()
    print("Does probing classifier τ alone suffice (D-tables only)?")
    for r in results:
        info = TABLES[r["name"]]
        tau = info.get("tau")
        if tau is not None:
            yes = columns_separate(info["table"], [tau])
            print(f"  {r['name']:<42} τ=col {tau}: {'YES' if yes else 'NO'}")

    # Check: rec_L == 2 via {s,r} for FRM tables?
    print()
    print("Does {s, r} retraction pair suffice (R-tables only)?")
    for r in results:
        info = TABLES[r["name"]]
        s, rv = info.get("s"), info.get("r")
        if s is not None and rv is not None:
            yes = columns_separate(info["table"], [s, rv])
            print(f"  {r['name']:<42} s={s},r={rv}: {'YES' if yes else 'NO'}")


if __name__ == "__main__":
    main()

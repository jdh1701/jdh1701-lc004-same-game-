#!/usr/bin/env python3
"""Exact ordinary-word W/U/B census; independent reference on raw cells."""
import argparse
import csv
import json
import sys
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path

here = Path(__file__).resolve()
script_dirs = [here.parents[1] / "public-lc004" / "scripts",
               here.parents[2] / "scripts",
               here.parents[1] / "scripts"]
script_dir = next((p for p in script_dirs if (p / "exhaustive_verify.py").exists()), None)
if script_dir is None:
    raise FileNotFoundError("public scripts/exhaustive_verify.py not found")
sys.path.insert(0, str(script_dir))
import exhaustive_verify as reference


def runs(w):
    out = []
    i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        out.append((w[i], j - i, i, j))
        i = j
    return out


def canon(colors):
    mapping = {}
    return tuple(mapping.setdefault(c, len(mapping)) for c in colors)


def state_key(s):
    def normalize(a):
        cs = canon([c for c, _ in a])
        return tuple(zip(cs, [h for _, h in a]))
    return min(normalize(s), normalize(s[::-1]))


@lru_cache(None)
def paths(s):
    if not s:
        return 1
    return sum(paths(t) for _, t in reference.run_moves(s))


def pair_signature(s, i, j):
    # Bounded local motif: selected run distance; each side's one-run context.
    # This is deliberately a coarse, explicitly specified invariant.
    window = sorted(set(k for z in (i, j) for k in (z - 1, z, z + 1)
                        if 0 <= k < len(s)))
    color_pattern = canon([s[k][0] for k in window])
    relabel = {k: v for v, k in enumerate(window)}
    spec = (min(j - i, 4), tuple((color_pattern[t], int(s[k][1]),
                                 int(k in (i, j)))
                                for t, k in enumerate(window)),
            i == 0, j == len(s) - 1,
            int(i > 0 and i + 1 < len(s) and s[i-1][0] == s[i+1][0]),
            int(j > 0 and j + 1 < len(s) and s[j-1][0] == s[j+1][0]))
    # Use a second reflected view to quotient reversal exactly.
    rev = s[::-1]
    ri, rj = len(s)-1-j, len(s)-1-i
    rw = sorted(set(k for z in (ri, rj) for k in (z-1, z, z+1)
                    if 0 <= k < len(s)))
    rc = canon([rev[k][0] for k in rw])
    reflected = (min(rj-ri, 4),
                 tuple((rc[t], int(rev[k][1]), int(k in (ri, rj)))
                       for t, k in enumerate(rw)),
                 ri == 0, rj == len(s)-1,
                 int(ri > 0 and ri+1 < len(s) and rev[ri-1][0] == rev[ri+1][0]),
                 int(rj > 0 and rj+1 < len(s) and rev[rj-1][0] == rev[rj+1][0]))
    return min(spec, reflected)


def census(q, n):
    arity = Counter()
    legal_hist = Counter()
    path_hist = Counter()
    geometry_hist = Counter()
    types = set()
    W = U = successful_bridges = successful_no_merge = 0
    first_branch = None
    for w in product(range(q), repeat=n):
        s = reference.encode_word(w)
        moves = reference.run_moves(s)
        good = [(i, t) for i, t in moves if paths(t)]
        legal_hist[len(moves)] += 1
        if not good:
            continue
        W += 1
        arity[len(good)] += 1
        p = paths(s)
        path_hist[str(p if p <= 100 else "101+")] += 1
        for i, _ in good:
            bridge = 0 < i < len(s)-1 and s[i-1][0] == s[i+1][0]
            successful_bridges += bridge
            successful_no_merge += not bridge
        if len(good) == 1:
            U += 1
        else:
            if first_branch is None:
                first_branch = "".join(map(str, w))
            types.add(state_key(s))
            for a, (i, _) in enumerate(good):
                for j, _ in good[a+1:]:
                    geometry_hist[str(pair_signature(s, i, j))] += 1
    return {
        "q": q, "n": n, "universe": "ordinary words with q labeled colors",
        "total": q**n, "W": W, "U": U, "B": W-U,
        "U_over_W": U/W if W else None, "B_over_W": (W-U)/W if W else None,
        "successful_first_arity": dict(sorted(arity.items())),
        "legal_first_arity_all_words": dict(sorted(legal_hist.items())),
        "successful_path_count_winners": dict(sorted(path_hist.items())),
        "successful_bridge_moves": successful_bridges,
        "successful_no_merge_moves": successful_no_merge,
        "canonical_B_states": len(types),
        "local_pair_geometry_types": len(geometry_hist),
        "local_pair_geometry_histogram": geometry_hist,
        "first_branching_example": first_branch,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ranges", default="2:15,3:12,4:10")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent / "results"))
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for item in args.ranges.split(","):
        q, nmax = map(int, item.split(":"))
        for n in range(1, nmax+1):
            row = census(q, n)
            rows.append(row)
            print(q, n, row["W"], row["U"], row["B"], row["canonical_B_states"],
                  row["local_pair_geometry_types"], flush=True)
    (out/"census.json").write_text(json.dumps(rows, indent=2, sort_keys=True)+"\n")
    fields = ["q", "n", "universe", "total", "W", "U", "B",
              "U_over_W", "B_over_W", "canonical_B_states",
              "local_pair_geometry_types", "successful_bridge_moves",
              "successful_no_merge_moves", "first_branching_example"]
    with (out/"census.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row[k] for k in fields})
    return rows


if __name__ == "__main__":
    main()

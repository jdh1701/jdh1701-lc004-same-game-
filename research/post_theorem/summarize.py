#!/usr/bin/env python3
"""Read saved census and emit pair summaries and a growth plot."""
import ast
import csv
import json
from collections import Counter
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parent / "results"
rows = json.loads((root / "census.json").read_text())
pair_rows = []
for r in rows:
    d = Counter()
    for key, count in r["local_pair_geometry_histogram"].items():
        dist, _, left_endpoint, right_endpoint, b1, b2 = ast.literal_eval(key)
        d["adjacent" if dist == 1 else "distance_2" if dist == 2
          else "distance_3" if dist == 3 else "distance_4_plus"] += count
        d["bridge_bridge" if b1 and b2 else
          "bridge_no_merge" if b1 or b2 else "no_merge_no_merge"] += count
        d["endpoint_involved" if left_endpoint or right_endpoint else
          "interior_pair"] += count
    pair_rows.append({"q": r["q"], "n": r["n"], **d})
fields = ["q", "n", "adjacent", "distance_2", "distance_3", "distance_4_plus",
          "bridge_bridge", "bridge_no_merge", "no_merge_no_merge",
          "endpoint_involved", "interior_pair"]
with (root / "pair_geometry_summary.csv").open("w", newline="") as f:
    wr = csv.DictWriter(f, fieldnames=fields)
    wr.writeheader()
    for r in pair_rows:
        wr.writerow(r)

fig, ax = plt.subplots(figsize=(8, 5))
for q in sorted(set(r["q"] for r in rows)):
    a = [r for r in rows if r["q"] == q and r["B"]]
    ax.plot([r["n"] for r in a], [r["canonical_B_states"] for r in a],
            marker="o", label=f"q={q}")
ax.set_yscale("log")
ax.set_xlabel("ordinary word length n")
ax.set_ylabel("distinct branching Boolean states, canonical under relabeling and reversal")
ax.set_title("Growth of observed branching-state classes")
ax.legend()
ax.grid(alpha=.25)
fig.tight_layout()
fig.savefig(root / "branching_state_growth.png", dpi=180)
print(root / "pair_geometry_summary.csv")
print(root / "branching_state_growth.png")

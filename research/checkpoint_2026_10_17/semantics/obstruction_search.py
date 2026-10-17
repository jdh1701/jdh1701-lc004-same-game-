#!/usr/bin/env python3
"""Exhaust minimal ambiguity hyperedges, without an assumed arity bound.

For each fixed palindromic skeleton the centre is heavy. At each subset
size, test precisely those extensions whose immediate subsets are unique.
Every ambiguous set encountered is therefore inclusion-minimal, provided
successful paths are monotone under heavy-bit upgrades. That monotonicity
is proved universally in LC004/PathMonotonicity.lean. This Python search is
an independently implemented finite computation, not a formal extraction.
"""
from collections import Counter
from pathlib import Path
import argparse
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'canonical'))
from experiments import restricted_growth
from orbit_experiments import cap_paths
from flag_conflicts import state


def run(q, mmax):
    start = time.monotonic()
    rows, witnesses = [], {}
    for m in range(1, mmax + 1):
        counts = Counter()
        tested = good = skeletons = 0
        for half in restricted_growth(m + 1, max_colors=q, normalized=True):
            skeletons += 1
            previous = {0}
            assert cap_paths(state(half, ())) == 1
            for size in range(1, 2 * m + 1):
                candidates = {mask | (1 << i) for mask in previous
                              for i in range(2 * m) if not mask >> i & 1}
                current = set()
                for mask in sorted(candidates):
                    positions = tuple(i for i in range(2 * m) if mask >> i & 1)
                    if not all(mask ^ (1 << i) in previous for i in positions):
                        continue
                    tested += 1
                    value = cap_paths(state(half, positions))
                    assert value in (1, 2)
                    if value == 1:
                        current.add(mask)
                        good += 1
                    else:
                        counts[size] += 1
                        if size not in witnesses:
                            witness = {'arity': size, 'shells': m, 'half': half,
                                       'outer_indices': positions,
                                       'actual_run_indices': [i + (i >= m) for i in positions],
                                       'runs': state(half, positions)}
                            witnesses[size] = witness
                            print(json.dumps({'new_arity': witness}), flush=True)
                previous = current
                if not previous:
                    break
        row = {'shells': m, 'skeletons': skeletons, 'tested_candidates': tested,
               'unique_nonempty_subsets': good,
               'minimal_ambiguity_counts_by_arity': dict(sorted(counts.items())),
               'elapsed_seconds': time.monotonic() - start}
        rows.append(row)
        result = {'q': q, 'completed_shell_bound': m, 'rows': rows,
                  'witnesses': list(witnesses.values()),
                  'scope': 'Finite exhaustive antichain search, not an arity-bound theorem.'}
        (HERE / 'data' / f'obstructions_q{q}.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--q', type=int, default=3)
    parser.add_argument('--mmax', type=int, default=8)
    args = parser.parse_args()
    run(args.q, args.mmax)

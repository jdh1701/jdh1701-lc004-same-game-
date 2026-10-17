#!/usr/bin/env python3
"""Test a proposed three-colour family; no finite run establishes the family."""
from pathlib import Path
import argparse
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'canonical'))
from orbit_experiments import cap_paths
from flag_conflicts import state, paths
from itertools import islice


def run(kmax):
    rows = []
    start = time.monotonic()
    for k in range(1, kmax + 1):
        half = tuple(x for j in range(k) for x in ((0,1,0) if j % 2 == 0 else (2,1,2)))
        m = 3 * k - 1
        actual = (1,) + tuple(range(3, 3*k, 3)) + (3*k,) + tuple(range(3*k+2, 6*k-3, 3))
        outer = tuple(i - (i > m) for i in actual)
        s = state(half, outer)
        base = cap_paths(state(half, ()))
        assert base == 1
        full = cap_paths(s)
        deleted = []
        for i in outer:
            value = cap_paths(state(half, tuple(j for j in outer if j != i)))
            deleted.append(value)
        row = {'k': k, 'runs': len(s), 'arity': len(outer), 'half': half,
               'actual_run_indices': actual, 'base_capped_count': base,
               'full_capped_count': full,
               'maximal_proper_capped_counts': deleted,
               'minimal': full == 2 and all(v == 1 for v in deleted),
               'seconds': time.monotonic() - start}
        if k <= 3:
            row['two_paths'] = list(islice(paths(s), 2))
        rows.append(row)
        (HERE/'data/chain_family.json').write_text(json.dumps(rows, indent=2)+'\n')
        print(json.dumps(row), flush=True)
        if not row['minimal']:
            raise AssertionError(('FAMILY CONJECTURE FALSIFIED', row))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--kmax', type=int, default=5)
    run(parser.parse_args().kmax)

#!/usr/bin/env python3
"""Independent raw-cell/exact-run checks on all 96 finite witness masks."""
from pathlib import Path
from itertools import islice
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'canonical'))
from experiments import encode, raw_paths, run_paths
from flag_conflicts import state, paths

records = []
for half, active in [((0,1,0,2,1,2,0,1,0), (1,3,6,8,10,13)),
                     ((0,1,2,0,1,0,1,0,2), (2,3,7,9,11))]:
    rows = []
    for mask in range(1 << len(active)):
        selected = tuple(i for j,i in enumerate(active) if mask >> j & 1)
        s = state(half, selected)
        raw = tuple(c for c,b in s for _ in range(1 + int(b)))
        assert encode(raw) == s
        a,b = raw_paths(raw),run_paths(s)
        assert a == b
        assert (a == 1) == (mask < (1 << len(active)) - 1)
        rows.append({'mask': mask, 'exact_paths': a})
    record = {'arity': len(active), 'half': half, 'outer_indices': active,
              'full_runs': s, 'full_raw': raw,
              'full_two_paths': list(islice(paths(s), 2)), 'mask_results': rows}
    records.append(record)
    print(json.dumps({'arity': len(active), 'checked_masks': len(rows),
                      'proper_counts': 1, 'full_count': a}), flush=True)
(HERE/'data/exact_witness_checks.json').write_text(json.dumps(records, indent=2)+'\n')

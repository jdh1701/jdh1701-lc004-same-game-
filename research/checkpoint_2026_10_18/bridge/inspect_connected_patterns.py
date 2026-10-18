#!/usr/bin/env python3
"""Reproduce the detailed connected-pattern census first run inline."""
from collections import Counter
import json
from pathlib import Path
from connected_weights import witnesses,signed_constraints,nc_components

HERE = Path(__file__).resolve().parent
rows = []
for n in (10,11,12):
    coeff,_ = signed_constraints(witnesses(n))
    terms = [dict(partition=p,coefficient=a,block_sizes=sorted(Counter(p).values()))
             for p,a in coeff.items()
             if len(set(p))>1 and len(nc_components(p))==1]
    rows.append(dict(n=n,terms=terms))
    print(json.dumps(dict(n=n,terms=len(terms),
        block_size_histogram=dict(Counter(str(t['block_sizes']) for t in terms)),
        small_blocks=[t for t in terms if min(t['block_sizes'])<5][:3])),flush=True)
(HERE/'data/connected_patterns.json').write_text(json.dumps(rows,indent=2)+'\n')

#!/usr/bin/env python3
"""Compare the direct C++ cell counts with existing and held-out polynomials."""
from pathlib import Path
import json
from connected_weights import orbit_moments

HERE = Path(__file__).resolve().parent
moments = orbit_moments(12)
held = json.loads((HERE/'data/holdout_length13.json').read_text())
moments.append({int(k):a for k,a in held['polynomial'].items()})
rows = []
for q in (3,4):
    raw = [json.loads(s) for s in (HERE/f'logs/raw_q{q}_n13.log').read_text().splitlines()]
    assert [r['n'] for r in raw] == list(range(14))
    for row in raw:
        assert row['q'] == q and row['words'] == q**row['n']
        expected = sum(a*q**k for k,a in moments[row['n']].items())
        assert row['winning'] == expected,(row,expected)
    rows += raw
result = dict(independent_raw_count_comparisons=len(rows),
              labelled_words_examined=sum(r['words'] for r in rows),
              q3_n13=rows[13]['winning'],q4_n13=rows[-1]['winning'],failures=0)
(HERE/'data/raw_crosscheck.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)

"""Cross-check fresh raw-cell counts against partition polynomials."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
rows=json.loads((HERE/'data/engine_checks.json').read_text())['rows']
rows.append(json.loads((HERE/'data/threshold15.json').read_text()))
inferred=json.loads((HERE/'data/inference15_from_raw.json').read_text())
assert rows[14]['prediction_matches']
assert not rows[15]['quadratic_rival_matches']
assert inferred['inferred_connected']==rows[15]['connected_polynomial']
assert inferred['inferred_q4']==rows[15]['q4']
assert len(rows[15]['three_or_more_block_terms'])==35
assert all(t['coefficient']==-1 and t['sizes']==[5,5,5]
           for t in rows[15]['three_or_more_block_terms'])
polys={r['n']:{int(k):a for k,a in r['polynomial'].items()} for r in rows}
comparisons=[]
for q,nmax in ((3,15),(4,14)):
    raw=[json.loads(s) for s in (HERE/f'logs/raw_q{q}_n{nmax}.log').read_text().splitlines()]
    assert [r['n'] for r in raw]==list(range(nmax+1))
    for r in raw:
        assert r['q']==q and r['words']==q**r['n']
        predicted=sum(a*q**k for k,a in polys[r['n']].items())
        assert r['winning']==predicted,(r,predicted)
        comparisons.append(r)
out=dict(comparisons=len(comparisons),labelled_words_examined=sum(r['words'] for r in comparisons),
    q3_n14=next(r['winning'] for r in comparisons if r['q']==3 and r['n']==14),
    q4_n14=comparisons[-1]['winning'],q3_n15=comparisons[15]['winning'],failures=0)
(HERE/'data/raw_crosscheck.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)

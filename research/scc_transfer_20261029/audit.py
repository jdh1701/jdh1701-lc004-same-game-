import json,math
from pathlib import Path
F=Path(__file__).parent
r20=json.loads((F/'result.json').read_text());r25=json.loads((F/'result25.json').read_text())
assert r20['survivors']==415 and r25['survivors']==6455
assert r20['weighted_survivors']==4*415 and r25['weighted_survivors']==5*6455
assert r25['templates4']==3769195 and r25['certificate_incidences4']==math.factorial(20)//(math.factorial(13)*math.factorial(4))==16279200
j=json.loads((F/'claude128_shard_audit.json').read_text())
assert j['run_id']==40942806037 and j['all_jobs_success']
for n,expected in [(20,415),(25,6455)]:
    rows=[v for r in j['records'] for v in r['counts'] if v['n']==n]
    assert len(rows)==128 and {r['shard'] for r in rows}==set(range(128))
    assert sum(r['count'] for r in rows)==expected
out=dict(status='VERIFIED-COMP',independent_counts={'20':415,'25':6455},claude_run=40942806037,claude_shards_checked=128,failures=0)
(F/'comparison_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))

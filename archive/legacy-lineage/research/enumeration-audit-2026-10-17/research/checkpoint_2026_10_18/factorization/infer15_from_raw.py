"""Conditional inference AFTER q=3 raw enumeration, BEFORE full joins finish."""
from pathlib import Path
from datetime import datetime,timezone
import json
HERE=Path(__file__).resolve().parent
rival=json.loads((HERE/'data/quadratic_rival15.json').read_text())
raw=json.loads((HERE/'logs/raw_q3_n15.log').read_text().splitlines()[-1])
assert raw['q']==3 and raw['n']==15
difference=raw['winning']-rival['quadratic_q3']
assert difference%6==0
c=difference//6
old={int(k):a for k,a in rival['quadratic_connected'].items()}
out=dict(created_utc=datetime.now(timezone.utc).isoformat(),
    evidence='Direct q=3 raw count completed; full n=15 partition calculation still running',
    assumption='connected polynomial has degree at most three',raw_q3=raw['winning'],
    quadratic_q3=rival['quadratic_q3'],difference=difference,
    inferred_connected={1:old[1]+2*c,2:old[2]-3*c,3:c},
    inferred_q4=rival['quadratic_q4']+24*c)
p=HERE/'data/inference15_from_raw.json'
if p.exists(): raise SystemExit('Refusing to overwrite inference record')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)

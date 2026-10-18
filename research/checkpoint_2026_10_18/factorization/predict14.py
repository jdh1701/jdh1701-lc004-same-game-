"""Freeze the n=14 prediction before the new partition/raw enumerations."""
from pathlib import Path
from datetime import datetime, timezone
import sys, json, hashlib
HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'bridge'))
from connected_weights import orbit_moments, formal_cumulants, add
from predict_length13 import fib, evaluate

old = orbit_moments(12)
old.append({int(k):a for k,a in json.loads(
    (HERE.parent/'bridge/data/holdout_length13.json').read_text())['polynomial'].items()})
n=14
known={k:-a for k,a in formal_cumulants(old+[{}])[n].items()}
two=2**n-2*n*fib(n-2)-(-1)**n-1
r1,r2=1-evaluate(known,1),two-evaluate(known,2)
assert (r2-2*r1)%2==0
b=(r2-2*r1)//2
connected={1:r1-b,2:b}
poly=add(known,connected)
out=dict(n=n,created_utc=datetime.now(timezone.utc).isoformat(),
    assumptions=['component factorization','minimum five positions per block in nontrivial connected support'],
    inputs='polynomials through 13 and known one-/two-colour values at 14',
    binary_count=two,connected_polynomial=connected,polynomial=poly,
    q3=evaluate(poly,3),q4=evaluate(poly,4),
    status='conditional prediction recorded before n=14 computations')
p=HERE/'data/prediction14.json'
if p.exists(): raise SystemExit('Refusing to overwrite prediction')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
print('sha256='+hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)

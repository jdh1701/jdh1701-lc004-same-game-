"""Discriminate continued quadratic connected weights from a new cubic term.

The five-position hypothesis first ALLOWS three connected blocks at n=15;
it does not require them. Record the quadratic rival before computing n=15.
"""
from collections import Counter
from pathlib import Path
import sys,json,hashlib,subprocess,time
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'bridge'))
from connected_weights import orbit_moments,formal_cumulants,add,witnesses,nc_components
from predict_length13 import fib,evaluate
from test_engine import pack,unpack

def predict():
    rows=json.loads((HERE/'data/engine_checks.json').read_text())['rows']
    moments=[{int(k):a for k,a in r['polynomial'].items()} for r in rows]
    assert len(moments)==15
    known={k:-a for k,a in formal_cumulants(moments+[{}])[15].items()}
    binary=2**15-30*fib(13)-(-1)**15-1
    r1,r2=1-evaluate(known,1),binary-evaluate(known,2)
    assert (r2-2*r1)%2==0
    b=(r2-2*r1)//2
    conn={1:r1-b,2:b}
    poly=add(known,conn)
    row=dict(n=15,created_utc=datetime.now(timezone.utc).isoformat(),
        rival='connected polynomial remains quadratic',
        structural_alternative='degree three is permitted, but not required, by five positions per block',
        quadratic_connected=conn,quadratic_polynomial=poly,
        quadratic_q3=evaluate(poly,3),quadratic_q4=evaluate(poly,4),
        binary_count=binary)
    p=HERE/'data/quadratic_rival15.json'
    if p.exists(): raise SystemExit('Refusing to overwrite rival prediction')
    p.write_text(json.dumps(row,indent=2)+'\n')
    print(json.dumps(row),flush=True)
    print('sha256='+hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)

def test():
    p=HERE/'data/quadratic_rival15.json'
    predicted=json.loads(p.read_text())
    ws=witnesses(15)
    print(json.dumps(dict(n=15,witnesses=len(ws),phase='begin')),flush=True)
    start=time.monotonic()
    inputs='15\n'+''.join(str(pack(w))+'\n' for w in ws)
    run=subprocess.run(['/tmp/samegame-partition-counter'],input=inputs,text=True,capture_output=True,check=True)
    coeff={unpack(int(k),15):int(a) for k,a in (line.split() for line in run.stdout.splitlines())}
    poly,conn,hist=Counter(),Counter(),Counter()
    small=[]
    three=[]
    for w,a in coeff.items():
        k=len(set(w)); poly[k]+=a
        if len(nc_components(w))==1:
            conn[k]+=a
            if k>1:
                sizes=tuple(sorted(Counter(w).values()))
                hist[sizes]+=1
                if min(sizes)<5: small.append(dict(partition=w,coefficient=a))
                if k>=3: three.append(dict(partition=w,coefficient=a,sizes=sizes))
    poly={k:a for k,a in sorted(poly.items()) if a}
    row=dict(n=15,engine=json.loads(run.stderr),polynomial=poly,connected_polynomial=dict(conn),
        connected_size_histogram={str(k):v for k,v in sorted(hist.items())},
        small_block_counterexamples=small,three_or_more_block_terms=three,
        quadratic_rival_matches=poly=={int(k):a for k,a in predicted['quadratic_polynomial'].items()},
        q3=evaluate(poly,3),q4=evaluate(poly,4),
        rival_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    (HERE/'data/threshold15.json').write_text(json.dumps(row,indent=2)+'\n')
    print(json.dumps(row),flush=True)

if __name__=='__main__':
    {'predict':predict,'test':test}[sys.argv[1]]()

"""Exact old-engine controls, then the prospectively predicted length 14.

The new C++ join engine shares only the Python witness generator with the old
engine. Raw-cell enumeration is a separate later check.
"""
from collections import Counter
from pathlib import Path
from math import prod
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'bridge'))
from connected_weights import witnesses,signed_constraints,nc_components,canonical

def pack(p): return sum(c<<(4*i) for i,c in enumerate(p))
def unpack(k,n): return tuple((k>>(4*i))&15 for i in range(n))

def main():
    prediction_path=HERE/'data/prediction14.json'
    prediction=json.loads(prediction_path.read_text())
    old=json.loads((HERE.parent/'data/partition_counts.json').read_text())['rows']
    expected={r['n']:{int(k):a for k,a in r['polynomial'].items()} for r in old}
    expected[13]={int(k):a for k,a in json.loads((HERE.parent/'bridge/data/holdout_length13.json').read_text())['polynomial'].items()}
    maps,rows={},[]
    for n in range(15):
        start=time.monotonic()
        ws=witnesses(n)
        inputs=str(n)+'\n'+''.join(str(pack(p))+'\n' for p in ws)
        run=subprocess.run(['/tmp/samegame-partition-counter'],input=inputs,text=True,capture_output=True,check=True)
        coeff={unpack(int(k),n):int(a) for k,a in (line.split() for line in run.stdout.splitlines())}
        assert len(coeff)==len(run.stdout.splitlines())
        if n<=10:
            reference,_=signed_constraints(ws)
            assert coeff==reference,('engine mismatch',n)
        poly=Counter()
        conn=Counter()
        small=[]
        factor_fail=[]
        factors=0
        hist=Counter()
        for p,a in coeff.items():
            poly[len(set(p))]+=a
            components=nc_components(p)
            if len(components)==1:
                conn[len(set(p))]+=a
                if len(set(p))>1:
                    sizes=tuple(sorted(Counter(p).values()))
                    hist[sizes]+=1
                    if min(sizes)<5: small.append(dict(partition=p,coefficient=a))
            elif n>0:
                predicted=prod(maps[len(ix)].get(canonical(tuple(p[i] for i in ix)),0) for ix in components)
                factors+=1
                if a!=predicted: factor_fail.append(dict(partition=p,actual=a,predicted=predicted))
        maps[n]=coeff
        poly={k:a for k,a in sorted(poly.items()) if a}
        if n<=13: assert poly==expected[n],('old polynomial',n,poly,expected[n])
        row=dict(n=n,engine=json.loads(run.stderr),polynomial=poly,connected_polynomial=dict(conn),
                 small_block_counterexamples=small,factorization_counterexamples=factor_fail,
                 nontrivial_support_factorizations=factors,
                 connected_size_histogram={str(k):v for k,v in sorted(hist.items())},
                 coefficient_map_sha256=hashlib.sha256(json.dumps(sorted(coeff.items())).encode()).hexdigest(),
                 q3=sum(a*3**k for k,a in poly.items()),q4=sum(a*4**k for k,a in poly.items()),
                 seconds=time.monotonic()-start)
        if n==14:
            row['prediction_matches']=poly=={int(k):a for k,a in prediction['polynomial'].items()}
            row['prediction_sha256']=hashlib.sha256(prediction_path.read_bytes()).hexdigest()
        rows.append(row)
        print(json.dumps(row),flush=True)
        (HERE/'data/engine_checks.json').write_text(json.dumps(dict(rows=rows,exact_map_control_lengths=list(range(11))),indent=2)+'\n')

if __name__=='__main__': main()

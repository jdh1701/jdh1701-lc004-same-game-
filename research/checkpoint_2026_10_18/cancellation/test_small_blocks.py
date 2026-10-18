"""Test small-block gap formulas, and attack extension to block size five.

Blocks containing position zero suffice after cyclic rotation, but that
rotation reduction is not assumed as a Lean theorem here.
"""
from collections import Counter
from itertools import combinations
from math import prod
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'bridge'))
from connected_weights import witnesses,signed_constraints,canonical
from experiments import restricted_growth,grammar_solvable
sys.path.insert(0,str(HERE.parent))
from partition_count import matches

def main():
    started=time.monotonic()
    maps={}
    counts=Counter()
    first_five=None
    for n in range(11):
        maps[n],_=signed_constraints(witnesses(n))
        # Rotations permute the full nonzero support, so inverse rotations
        # also rule out any zero-to-nonzero exception in this tested range.
        for p,a in maps[n].items():
            for k in range(n):
                assert maps[n].get(canonical(p[k:]+p[:k]),0)==a
                counts['rotation_support_checks']+=1
        for m in (2,3,4,5):
            if m>n:continue
            for tail in combinations(range(1,n),m-1):
                block=(0,)+tail
                rest=[i for i in range(n) if i not in block]
                for r in restricted_growth(n-m):
                    p=[0]*n
                    for i,c in zip(rest,r):p[i]=c+1
                    p=tuple(p)
                    gaps=[p[block[i]+1:block[i+1]] for i in range(m-1)]+[p[block[-1]+1:]]
                    seen={}
                    separated=True
                    for k,g in enumerate(gaps):
                        for c in g:
                            if c in seen and seen[c]!=k:separated=False
                            seen[c]=k
                    base={2:1,3:1,4:-1,5:-4}[m]
                    predicted=base*prod(maps[len(g)].get(canonical(g),0) for g in gaps) if separated else 0
                    actual=maps[n].get(p,0)
                    if m<=4:
                        assert actual==predicted,('coefficient formula',p,m,actual,predicted)
                        counts[f'block_{m}_coefficient_checks']+=1
                        counts['crossing_zero_checks']+=not separated
                    elif actual!=predicted and first_five is None:
                        first_five=dict(n=n,partition=p,actual=actual,small_block_prediction=predicted)
                    if m==4:
                        a,b,c,d=block
                        wa=wb=False
                        for w in witnesses(n):
                            if matches(w,p):
                                wa|=w[a]==w[b] and w[c]==w[d]
                                wb|=w[a]==w[d] and w[b]==w[c]
                        g1,g2,g3,g4=gaps
                        fa=grammar_solvable(g1) and grammar_solvable(g3) and grammar_solvable(g2+g4)
                        fb=grammar_solvable(g2) and grammar_solvable(g4) and grammar_solvable(g1+g3)
                        both=all(grammar_solvable(g) for g in gaps)
                        assert wa==fa and wb==fb and (wa and wb)==both,('pairing identity',p)
                        counts['four_block_pairing_checks']+=1
        print(json.dumps(dict(n=n,checks=dict(counts))),flush=True)
    assert first_five is not None
    out=dict(max_n=10,checks=dict(counts),size_five_counterexample=first_five,
             unexpected_failures=0,seconds=time.monotonic()-started)
    (HERE/'data/small_block_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()

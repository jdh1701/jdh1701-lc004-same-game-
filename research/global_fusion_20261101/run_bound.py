"""Exact checks for the run-normalized fusion majorant (not winner counts)."""
from collections import defaultdict
from itertools import groupby,product
from fractions import Fraction
from pathlib import Path
import json
from fusion import support,weighted_totals

def run_weight(w):
    cur={():1}
    for a,g in groupby(w):
        heavy=len(list(g))>=2;nxt=defaultdict(int)
        for s,c in cur.items():
            if heavy:nxt[s]+=c
            if s and s[-1]==a:
                nxt[s]+=c;nxt[s[:-1]]+=c
            else:nxt[s+(a,)]+=c
        cur=nxt
    return dict(cur)

def majorant_series(q,N):
    def mul(a,b):
        return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(N+1)]
    P=([1,-1,1,-1,1]+[0]*N)[:N+1];Q=P[:]
    if N>=4:Q[4]-=q
    inv=[1]+[0]*N
    for k in range(1,N+1):inv[k]=-sum(Q[j]*inv[k-j] for j in range(1,k+1))
    arg=mul(([0,1,-1]+[0]*N)[:N+1],inv)
    power=[1]+[0]*N;res=[0]*(N+1)
    for c in weighted_totals(q,N):
        res=[a+c*b for a,b in zip(res,power)];power=mul(power,arg)
    return mul(mul(P,inv),res)

def involution_support(w):
    # Rejected shortcut: capped heavy runs in the free product of Z/2.
    cur={()}
    for a,g in groupby(w):
        heavy=len(list(g))>=2;nxt=set(cur) if heavy else set()
        for s in cur:nxt.add(s[:-1] if s and s[-1]==a else s+(a,))
        cur=nxt
    return cur

def check():
    rows=[];checks=0
    for q,N in [(2,10),(3,9),(4,7)]:
        vals=[]
        for n in range(N+1):
            total=0
            for w in product(range(q),repeat=n):
                c=run_weight(w)
                assert frozenset(c)==support(w)
                total+=c.get((),0);checks+=1
            vals.append(total)
        pred=majorant_series(q,N);assert vals==pred
        rows.append({'q':q,'max_n':N,'majorant_coefficients':vals})
    w=(0,1,1,0,2,2,0)
    assert () in support(w) and () not in involution_support(w)
    assert run_weight((0,0,1,1,0,0))[()]==2
    r=Fraction(41,200);P=1-r+r*r-r**3+r**4;Q=P-5*r**4;gap=Q-5*r*(1-r)
    assert gap>0 and P/gap<129 and 1/(5*r)==Fraction(40,41)
    # A sharper capped-run witness bound still does not settle q=3 or q=4.
    result={'status':'VERIFIED-COMP','word_support_checks':checks,'series_replays':rows,
      'involution_counterexample':w,'run_majorant_overcount_word':[0,0,1,1,0,0],
      'five_color_certificate':{'r':str(r),'P':str(P),'Q':str(Q),'gap':str(gap),
        'P_over_gap':str(P/gap),'density_rate':str(1/(5*r))},
      'scope':'Finite checks supporting a paper proof; no Lean proof of the generating function or asymptotic bound.'}
    Path(__file__).with_name('run-bound-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':check()

#!/usr/bin/env python3
"""A conjectured exact binary unique-path classification, with held-out tests.

This is experimental evidence. Neither the classifier nor its counting formula
is claimed as a Lean theorem about Same Game.
"""
from collections import Counter
from itertools import product
from math import comb
from pathlib import Path
import csv
import json
import time
from experiments import encode, coeff_weight
from orbit_experiments import cap_paths, canon_runs

ROOT=Path(__file__).resolve().parent


def classifier(s):
    if not s:
        return True  # Empty word has one empty successful path.
    if len(s)%2==0:
        return False
    m=len(s)//2
    if not s[m][1]:
        return False
    if m==0:
        return True
    return (not (s[0][1] and s[-1][1]) and
            (not any(b for _,b in s[1:m]) or
             not any(b for _,b in s[m+1:-1])))


def flag_coeff(m,h):
    if m==0:
        return int(h==0)
    def c(n,k):return comb(n,k) if 0<=k<=n else 0
    # F_m(t)=(1+2t)*(2*(1+t)^(m-1)-1).
    return 2*c(m-1,h)+4*c(m-1,h-1)-int(h==0)-2*int(h==1)


def predicted_raw_count(n):
    if n==0:return 1
    return 2*sum(flag_coeff(m,h)*coeff_weight(n,2*m-h,h+1)
                 for m in range(max(0,(n-2)//2)+1) for h in range(m+1))


def run():
    start=time.monotonic();rows=[]
    # m<=7 generated the weighted-polynomial conjecture; m=8,9,10 are holdouts.
    for m in range(11):
        hist=Counter();checks=0
        for bits in product((False,True),repeat=2*m):
            flags=bits[:m]+(True,)+bits[m:]
            s=tuple((i%2,b) for i,b in enumerate(flags))
            actual=cap_paths(canon_runs(s))==1
            assert actual==classifier(s),('binary_classifier',s,actual)
            if actual:hist[sum(flags)-1]+=1
            checks+=1
        assert all(hist[h]==flag_coeff(m,h) for h in range(m+1))
        row={'shells':m,'runs':2*m+1,'flag_assignments':checks,
             'unique':sum(hist.values()),'by_heavy_runs':dict(hist),
             'held_out':m>=8}
        rows.append(row);print(json.dumps(row),flush=True)
    # Independent raw-word comparison: training counts through n=14, then
    # held-out lengths 15..18; cap_paths is still the exact deletion solver.
    raw=[]
    for n in range(15,19):
        count=0
        for w in product(range(2),repeat=n):
            s=encode(w);actual=cap_paths(canon_runs(s))==1
            assert actual==classifier(s),('raw_binary_classifier',w)
            count+=actual
        assert count==predicted_raw_count(n),(n,count,predicted_raw_count(n))
        raw.append({'n':n,'total':2**n,'unique':count,'held_out':True})
        print(json.dumps(raw[-1]),flush=True)
    out={'status':'CONJECTURE — finite evidence, not universal proof',
         'normalized_rows':rows,'raw_holdout':raw,'failures':0,
         'seconds':time.monotonic()-start}
    (ROOT/'data/binary_unique_conjecture.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'failures':0,'seconds':out['seconds']}),flush=True)


if __name__=='__main__':
    run()

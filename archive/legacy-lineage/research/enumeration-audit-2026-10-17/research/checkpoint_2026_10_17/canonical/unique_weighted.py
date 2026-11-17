#!/usr/bin/env python3
"""Count unique raw words via the Lean-proved necessary colour palindrome.

Not all palindromes are unique: the exact game-tree solver still decides that.
No mirror flag exclusions or fitted recurrences are assumed. Finite enumeration,
not a fixed-size transfer matrix, and not all winning-word enumeration.
"""
from collections import Counter
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import csv
import json
import sys
import time

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
sys.path.insert(0,str(PARENT))
from experiments import coeff_weight, restricted_growth, run_moves
from orbit_experiments import cap_paths, canon_runs
from binary_unique_conjecture import predicted_raw_count


def median_follow(s):
    moves=tuple(range((len(s)+1)//2-1,-1,-1))
    for i in moves:
        successor=dict(run_moves(s)).get(i)
        if successor is None:return None
        s=successor
    return s


def count(q,nmax):
    start=time.monotonic()
    orbits=Counter();attempts=unique=branching=0
    for m in range(max(0,(nmax-2)//2)+1):
        before=attempts;found=0
        for half in restricted_growth(m+1,max_colors=q,normalized=True):
            colours=half+half[-2::-1]
            k=max(half)+1
            for h in range(min(2*m,nmax-2*m-2)+1):
                for heavy in combinations(range(2*m),h):
                    flags=[False]*(2*m+1);flags[m]=True
                    for position in heavy:
                        flags[position+(position>=m)]=True
                    s=tuple(zip(colours,flags))
                    attempts+=1
                    p=cap_paths(s)
                    assert median_follow(s)==(),('palindrome_median_failure',s)
                    assert p>=1
                    if p==1:
                        orbits[m,h,k]+=1;unique+=1;found+=1
                    else:branching+=1
        print(json.dumps({'q':q,'shells':m,'candidates':attempts-before,
                          'unique_candidates':found,'elapsed':time.monotonic()-start}),flush=True)
    counts=[0]*(nmax+1);counts[0]=1
    for (m,h,k),number in orbits.items():
        orbit_weight=prod(q-i for i in range(k))
        for n in range(2*m+2+h,nmax+1):
            counts[n]+=number*orbit_weight*coeff_weight(n,2*m-h,h+1)
    # Direct raw-string experiments are independent of the palindrome filter.
    with (PARENT/'data/raw_counts.csv').open() as f:
        for row in csv.DictReader(f):
            if int(row['q'])==q and int(row['n'])<=nmax:
                assert counts[int(row['n'])]==int(row['unique']),row
    # The earlier general RGS census used no palindrome or median prefilter.
    general=Counter()
    with (PARENT/'data/orbit_polynomials.csv').open() as f:
        for row in csv.DictReader(f):
            n,k=int(row['n']),int(row['k'])
            if k<=q:general[n]+=int(row['unique_orbits'])*prod(q-i for i in range(k))
    assert all(counts[n]==v for n,v in general.items() if n<=nmax)
    if q==2:
        assert counts==[predicted_raw_count(n) for n in range(nmax+1)]
    previous={3:{11:2709,12:6057,13:13521},4:{10:4636,11:11980}}
    for n,v in previous.get(q,{}).items():
        if n<=nmax:assert counts[n]==v,(q,n,counts[n],v)
    assert attempts==unique+branching
    return {'q':q,'nmax':nmax,'counts':counts,'canonical_candidates':attempts,
            'unique_candidates':unique,'branching_candidates':branching,
            'seconds':time.monotonic()-start,'failures':0,
            'solver_cache':str(cap_paths.cache_info()),
            'unique_orbit_rows':[{'shells':m,'heavy_outer_runs':h,'colours':k,'orbits':v}
                                 for (m,h,k),v in sorted(orbits.items())]}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--q',type=int,required=True)
    parser.add_argument('--nmax',type=int,required=True)
    args=parser.parse_args()
    assert args.q>=1 and args.nmax>=2
    result=count(args.q,args.nmax)
    (HERE/'data'/f'unique_q{args.q}_n{args.nmax}.json').write_text(json.dumps(result,indent=2)+'\n')
    with (HERE/'data'/f'unique_q{args.q}_n{args.nmax}.csv').open('w') as f:
        out=csv.writer(f,lineterminator='\n');out.writerow(['q','n','unique_raw_words'])
        out.writerows((args.q,n,v) for n,v in enumerate(result['counts']))
    print(json.dumps({k:v for k,v in result.items() if k!='unique_orbit_rows'}),flush=True)


if __name__=='__main__':main()

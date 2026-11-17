#!/usr/bin/env python3
"""Exact colour-orbit polynomials; no reversal quotient or interpolation."""
from collections import Counter
from functools import lru_cache
from math import prod
from pathlib import Path
import csv
import json
import time
from experiments import encode, run_moves, raw_paths, restricted_growth

ROOT = Path(__file__).resolve().parent


def canon_runs(s):
    labels = {}
    return tuple((labels.setdefault(c,len(labels)),b) for c,b in s)


@lru_cache(maxsize=300000)
def cap_paths(s):
    if not s:
        return 1
    answer = 0
    for _,t in run_moves(s):
        answer += cap_paths(canon_runs(t))
        if answer>=2:
            return 2
    return answer


def no_singleton_partitions(n):
    """RGS words with every colour used >=2. Prune only impossible completions."""
    def visit(w, counts, singletons):
        remaining = n-len(w)
        if singletons > remaining:
            return
        if not remaining:
            yield w
            return
        for c in range(len(counts)):
            was_one = counts[c]==1
            counts[c]+=1
            yield from visit(w+(c,),counts,singletons-was_one)
            counts[c]-=1
        if singletons+1 <= remaining-1:
            counts.append(1)
            yield from visit(w+(len(counts)-1,),counts,singletons+1)
            counts.pop()
    yield from visit((),[],0)


def eval_orbits(counts,q):
    return sum(v*prod(q-i for i in range(k)) for k,v in counts.items() if k<=q)


def run(nmax=12):
    start=time.monotonic()
    rows=[];checks=0
    direct={}
    with (ROOT/'data/raw_counts.csv').open() as f:
        for row in csv.DictReader(f):
            direct[int(row['q']),int(row['n'])]=row
    for n in range(nmax+1):
        total=0;wins=Counter();unique=Counter()
        for w in no_singleton_partitions(n):
            total+=1;k=len(set(w));p=cap_paths(encode(w))
            wins[k]+=p>0;unique[k]+=p==1
            if n<=8:
                assert min(2,raw_paths(w))==p
                checks+=1
        for q in (2,3,4):
            if (q,n) in direct:
                assert eval_orbits(wins,q)==int(direct[q,n]['solvable'])
                assert eval_orbits(unique,q)==int(direct[q,n]['unique'])
        for k in range(n//2+1):
            rows.append(dict(n=n,k=k,solvable_orbits=wins[k],unique_orbits=unique[k]))
        print(json.dumps(dict(n=n,no_singleton_orbits=total,winning=dict(wins),
                              unique=dict(unique))),flush=True)
    with (ROOT/'data/orbit_polynomials.csv').open('w') as f:
        out=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');out.writeheader();out.writerows(rows)
    print(json.dumps(dict(failures=0,raw_crosschecks=checks,
                          cache=str(cap_paths.cache_info()),seconds=time.monotonic()-start)),flush=True)


if __name__=='__main__':
    run()

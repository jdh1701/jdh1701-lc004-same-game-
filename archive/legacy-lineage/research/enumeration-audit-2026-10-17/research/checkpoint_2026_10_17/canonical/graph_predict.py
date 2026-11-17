#!/usr/bin/env python3
"""Independent-set prediction compared to unfiltered exact uniqueness data.

This tests a structural conjecture. Graph coefficients are never substituted
for the reference data in unique_weighted.py.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import json,time,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from experiments import restricted_growth
from orbit_experiments import cap_paths
from flag_conflicts import state,paths
from itertools import islice


def independence_poly(adj,limit):
    @lru_cache(None)
    def rec(mask):
        if not mask:return (1,)+(0,)*limit
        vertices=[i for i in range(len(adj)) if mask>>i&1]
        v=max(vertices,key=lambda i:(adj[i]&mask).bit_count())
        if not (adj[v]&mask):
            return tuple(comb(len(vertices),h) if h<=len(vertices) else 0
                         for h in range(limit+1))
        excluded=rec(mask&~(1<<v))
        included=rec(mask&~((1<<v)|adj[v]))
        return tuple(excluded[h]+(included[h-1] if h else 0) for h in range(limit+1))
    return rec((1<<len(adj))-1)


def run(q,nmax):
    start=time.monotonic();predicted=Counter();rows=[];pair_checks=0
    actual=json.loads((HERE/'data'/f'unique_q{q}_n{nmax}.json').read_text())
    reference=Counter({(r['shells'],r['heavy_outer_runs'],r['colours']):r['orbits']
                       for r in actual['unique_orbit_rows']})
    for m in range((nmax-2)//2+1):
        limit=min(2*m,nmax-2*m-2);patterns=edges=0
        for half in restricted_growth(m+1,max_colors=q,normalized=True):
            patterns+=1;k=max(half)+1;adj=[0]*(2*m)
            if limit>=1:
                for i in range(2*m):
                    assert cap_paths(state(half,(i,)))==1
            if limit>=2:
                for i,j in combinations(range(2*m),2):
                    pair_checks+=1
                    if cap_paths(state(half,(i,j)))==2:
                        adj[i]|=1<<j;adj[j]|=1<<i;edges+=1
            poly=independence_poly(adj,limit)
            for h,c in enumerate(poly):predicted[m,h,k]+=c
        mismatches=[{'shells':m,'heavy_outer_runs':h,'colours':k,
                     'predicted':predicted[m,h,k],'actual':reference[m,h,k]}
                    for (mm,h,k) in set(reference)|set(predicted)
                    if mm==m and predicted[m,h,k]!=reference[m,h,k]]
        row={'q':q,'shells':m,'patterns':patterns,'bad_pairs':edges,
             'mismatches':mismatches,'seconds':time.monotonic()-start}
        rows.append(row);print(json.dumps(row),flush=True)
        if mismatches:
            # Locate an actual source witnessing an interaction beyond pairs.
            first=min(mismatches,key=lambda r:(r['heavy_outer_runs'],r['colours']))
            h=first['heavy_outer_runs'];k=first['colours']
            for half in restricted_growth(m+1,max_colors=q,normalized=True):
                if max(half)+1!=k:continue
                bad=[frozenset(pair) for pair in combinations(range(2*m),2)
                     if cap_paths(state(half,pair))==2]
                for heavy in combinations(range(2*m),h):
                    if any(pair.issubset(heavy) for pair in bad):continue
                    s=state(half,heavy)
                    if cap_paths(s)==2:
                        proper=[{'heavy':sub,'capped_path_count':cap_paths(state(half,sub))}
                                for size in range(h) for sub in combinations(heavy,size)]
                        assert all(r['capped_path_count']==1 for r in proper)
                        raw=tuple(c for c,b in s for _ in range(2 if b else 1))
                        out={'status':'PAIRWISE GRAPH CONJECTURE FALSIFIED',
                          'q':q,'nmax':nmax,'half':half,'runs':s,'heavy':heavy,
                          'shortest_raw_representative':raw,'raw_length':len(raw),
                          'all_proper_heavy_subsets':proper,
                          'successful_paths':list(islice(paths(s),2)),
                          'rows':rows,'seconds':time.monotonic()-start}
                        (HERE/'data'/f'graph_prediction_q{q}.json').write_text(json.dumps(out,indent=2)+'\n')
                        print(json.dumps(out),flush=True);return
            raise AssertionError('Mismatch found but no higher-order witness located')
    out={'status':'ALL TESTED AGGREGATE COEFFICIENTS MATCH; NOT A UNIVERSAL PROOF',
         'q':q,'nmax':nmax,'pair_checks':pair_checks,'rows':rows,
         'seconds':time.monotonic()-start}
    (HERE/'data'/f'graph_prediction_q{q}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out),flush=True)


if __name__=='__main__':
    run(3,22)
    cap_paths.cache_clear()
    run(4,18)

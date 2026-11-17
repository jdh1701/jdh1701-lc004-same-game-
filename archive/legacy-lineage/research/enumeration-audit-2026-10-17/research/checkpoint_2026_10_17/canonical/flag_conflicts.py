#!/usr/bin/env python3
"""Falsify pairwise-only flag interactions on palindromic colour skeletons.

The conjecture is tested, never assumed for the weighted enumeration.
"""
from itertools import combinations,islice
from pathlib import Path
import json,sys,time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from experiments import restricted_growth,run_moves
from orbit_experiments import cap_paths,canon_runs


def state(half,heavy):
    m=len(half)-1
    colours=half+half[-2::-1]
    flags=[False]*(2*m+1);flags[m]=True
    for i in heavy:flags[i+(i>=m)]=True
    return tuple(zip(colours,flags))


def paths(s):
    if not s:
        yield ()
    else:
        for i,t in run_moves(s):
            if cap_paths(canon_runs(t)):
                for p in paths(t):yield (i,)+p


def run():
    start=time.monotonic();tested=0;rows=[]
    for q,mmax in ((3,7),(4,5)):
        for m in range(1,mmax+1):
            skeletons=pair_count=triples=0
            for half in restricted_growth(m+1,max_colors=q,normalized=True):
                skeletons+=1;bad_pairs=set()
                for i in range(2*m):
                    s=state(half,(i,));tested+=1
                    assert cap_paths(s)==1,('single_extra_heavy_already_branches',s)
                for pair in combinations(range(2*m),2):
                    s=state(half,pair);tested+=1
                    if cap_paths(s)==2:bad_pairs.add(frozenset(pair))
                pair_count+=len(bad_pairs)
                for triple in combinations(range(2*m),3):
                    if any(pair.issubset(triple) for pair in bad_pairs):continue
                    triples+=1;s=state(half,triple);tested+=1
                    if cap_paths(s)==2:
                        witness={'status':'PAIRWISE CONJECTURE FALSIFIED',
                          'q_bound':q,'shells':m,'half':half,'runs':s,
                          'heavy_outer_positions':triple,'bad_pairs':list(map(sorted,bad_pairs)),
                          'successful_paths':list(islice(paths(s),2)),
                          'tested_candidates_before_counterexample':tested,
                          'seconds':time.monotonic()-start,'rows':rows}
                        (HERE/'data/flag_conflict_test.json').write_text(json.dumps(witness,indent=2)+'\n')
                        print(json.dumps(witness),flush=True);return
            row={'q_bound':q,'shells':m,'skeletons':skeletons,
                 'bad_pairs':pair_count,'triples_without_bad_pair_checked':triples}
            rows.append(row);print(json.dumps(row),flush=True)
    result={'status':'NO COUNTEREXAMPLE IN STATED DOMAIN; NOT A PROOF',
            'tested_candidates':tested,'rows':rows,'seconds':time.monotonic()-start}
    (HERE/'data/flag_conflict_test.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':run()

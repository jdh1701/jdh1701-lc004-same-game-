#!/usr/bin/env python3
"""Discriminating structural tests and explicit failed decompositions."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import time
from experiments import encode, raw_paths, raw_moves, run_moves, all_paths
from orbit_experiments import cap_paths, canon_runs

ROOT=Path(__file__).resolve().parent


def run():
    start=time.monotonic()
    failures={}
    # Exhaust binary words in increasing length, preserving minimal witnesses.
    for n in range(1,11):
        for w in product(range(2),repeat=n):
            p=raw_paths(w)
            if not p:
                continue
            if 'leftmost_greedy' not in failures:
                _,v=next(raw_moves(w))
                if not raw_paths(v):
                    failures['leftmost_greedy']={'word':w,'greedy_child':v,
                                                'successful_paths':all_paths(encode(w))}
            if 'shortest_solvable_prefix' not in failures:
                cut=next(i for i in range(1,n+1) if raw_paths(w[:i]))
                if not raw_paths(w[cut:]):
                    failures['shortest_solvable_prefix']={'word':w,'cut':cut,
                                                        'prefix':w[:cut],'suffix':w[cut:]}
            if 'rotation_preserves_unique_paths' not in failures and p==1:
                for i in range(1,n):
                    v=w[i:]+w[:i]
                    if raw_paths(v)!=1:
                        failures['rotation_preserves_unique_paths']={
                            'word':w,'rotation':v,'rotation_paths':raw_paths(v)}
                        break
    # Distinct colours on each shell and at the centre. This is a restricted
    # family, so checking all 2^(2m) flag assignments is inexpensive.
    tested=0;binary=[]
    for m in range(8):
        colors=tuple(range(m+1))+tuple(range(m-1,-1,-1))
        distribution=Counter()
        for bits in product((False,True),repeat=2*m):
            flags=bits[:m]+(True,)+bits[m:]
            s=tuple(zip(colors,flags))
            p=cap_paths(canon_runs(s))
            predicted=all(not(flags[i] and flags[-1-i]) for i in range(m))
            assert (p==1)==predicted,('distinct_shell',s,p,predicted)
            tested+=1
        # Binary palette: same test mechanism, but allow repetitions across
        # shell levels. Save the heavy-flag generating polynomials as evidence.
        if m<=7:
            colors=tuple(i%2 for i in range(2*m+1))
            for bits in product((False,True),repeat=2*m):
                flags=bits[:m]+(True,)+bits[m:]
                if any(flags[i] and flags[-1-i] for i in range(m)):
                    continue
                s=tuple(zip(colors,flags))
                if cap_paths(canon_runs(s))==1:
                    distribution[sum(flags)-1]+=1
            binary.append({'shells':m,'by_heavy_shell_runs':dict(distribution),
                           'total':sum(distribution.values())})
        print(json.dumps({'shells':m,'distinct_flag_assignments':4**m,
                          'binary_unique':binary[-1]}),flush=True)
    result={'failed_hypotheses':failures,'distinct_shell_assignments':tested,
            'binary_flag_polynomials':binary,'verification_failures':0,
            'seconds':time.monotonic()-start}
    (ROOT/'data/hypothesis_tests.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    run()

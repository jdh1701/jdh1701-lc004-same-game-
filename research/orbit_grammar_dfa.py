"""Color-permutation quotient of direct CFG determinization."""
from collections import defaultdict
from functools import lru_cache
from itertools import permutations
from time import perf_counter
import argparse
S=-1
def compute(q,n,verbose=False):
    perms=tuple(permutations(range(q)))
    @lru_cache(None)
    def canonical(states):
        # IMPORTANT: sort and lexicographically compare tuples, not frozensets.
        return frozenset(min(tuple(sorted(tuple(p[c] if c>=0 else S for c in st)
                                        for st in states)) for p in perms))
    @lru_cache(None)
    def closure(configs,remain):
        out=set();work=list(configs)
        while work:
            st=work.pop()
            if st in out or sum(c>=0 for c in st)>remain:continue
            out.add(st)
            if st and st[0]==S:
                tail=st[1:];work.append(tail)
                if remain>=2:
                    for a in range(q):
                        work.append((a,S,a,S)+tail)
                        if remain>=3:work.append((a,S,a,S,a,S)+tail)
        return frozenset(out)
    current={canonical(closure(frozenset({(S,)}),n)):1}
    levels=[1];edges=0
    for i in range(n):
        nxt=defaultdict(int)
        for state,count in current.items():
            for a in range(q):
                target=frozenset(st[1:] for st in state if st and st[0]==a)
                if not target:continue
                new=canonical(closure(target,n-i-1))
                nxt[new]+=count;edges+=1
        current=nxt;levels.append(len(current))
        if verbose:print(i+1,len(current),sum(current.values()),flush=True)
    return sum(c for st,c in current.items() if () in st),levels,edges,closure.cache_info().currsize

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--q',type=int,default=3);p.add_argument('--n',type=int,default=12);args=p.parse_args()
    t=perf_counter();count,levels,edges,cached=compute(args.q,args.n,True)
    print({'q':args.q,'n':args.n,'count':count,'states':levels,'edges':edges,
           'closures':cached,'seconds':round(perf_counter()-t,3)})

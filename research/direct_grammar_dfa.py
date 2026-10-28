"""Direct deterministic counting for the proposed Same Game grammar.
S -> epsilon | a S a S | a S a S a S
Unlike earlier minimization experiments, this NEVER enumerates winning words.
It counts distinct words by merging sets of viable parser-stack configurations.
The grammar-to-actual-game equivalence remains unproved generally.
"""
from collections import defaultdict
from functools import lru_cache
from time import perf_counter
import argparse
S=-1

def compute(q,n,verbose=False,cap=200000):
    @lru_cache(None)
    def closure(configs,remain):
        out=set()
        work=list(configs)
        while work:
            st=work.pop()
            if st in out or sum(c>=0 for c in st)>remain:
                continue
            out.add(st)
            if st and st[0]==S:
                tail=st[1:]
                work.append(tail)
                if remain>=2:
                    for a in range(q):
                        work.append((a,S,a,S)+tail)
                        if remain>=3:
                            work.append((a,S,a,S,a,S)+tail)
        return frozenset(out)
    current={closure(frozenset({(S,)}),n):1}
    levels=[len(current)]
    edges=0
    for pos in range(n):
        nxt=defaultdict(int)
        for state,count in current.items():
            for a in range(q):
                targets=frozenset(st[1:] for st in state if st and st[0]==a)
                if not targets:continue
                ns=closure(targets,n-pos-1)
                if not ns:continue
                nxt[ns]+=count
                edges+=1
        current=nxt
        levels.append(len(current))
        if verbose:
            print('depth',pos+1,'states',len(current),'path_count',sum(current.values()),
                  'cached_closures',closure.cache_info().currsize,flush=True)
        if len(current)>cap:raise RuntimeError('state cap exceeded')
    accepted=sum(c for st,c in current.items() if () in st)
    return accepted,levels,edges,closure.cache_info().currsize

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--q',type=int,default=3)
    p.add_argument('--n',type=int,default=12)
    p.add_argument('--cap',type=int,default=200000)
    args=p.parse_args()
    t=perf_counter()
    count,levels,edges,closed=compute(args.q,args.n,True,args.cap)
    print('FINAL',{'q':args.q,'n':args.n,'grammar_distinct_words':count,
                   'states_per_level':levels,'transitions':edges,
                   'closures':closed,'seconds':round(perf_counter()-t,3)})

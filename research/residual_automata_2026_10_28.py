from functools import lru_cache
from itertools import product
from collections import Counter
@lru_cache(None)
def win(w):
    if not w:return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2 and win(w[:i]+w[j:]):return True
        i=j
    return False
def experiment(q,n):
    root={}; winners=0
    for w in product(range(q),repeat=n):
        if not win(w):continue
        winners+=1; node=root
        for c in w:node=node.setdefault(c,{})
    raw=Counter(); states=[]; intern={}
    def fold(node,d):
        raw[d]+=1
        tr=tuple((c,fold(t,d+1)) for c,t in sorted(node.items()))
        key=(d,tr)
        if key not in intern:
            intern[key]=len(states); states.append((d,tr))
        return intern[key]
    start=fold(root,0)
    @lru_cache(None)
    def count(s):
        d,tr=states[s]
        return 1 if d==n else sum(count(t) for _,t in tr)
    assert count(start)==winners
    return n,winners,sum(raw.values()),len(states)
if __name__=='__main__':
    for n in range(4,13):print(experiment(3,n),flush=True)
    for q,n in [(2,10),(2,12),(4,8),(4,9)]:print(q,experiment(q,n),flush=True)

"""Independent combinatorial enumeration of the second diagonal.
Enumerates noncrossing matchings merged in two pairs, and noncrossing
partitions with exactly two triple blocks. Checks generated words against
the original maximal-run game, but completeness for ALL winning words
remains a mathematical proof obligation.
"""
from functools import lru_cache
from itertools import combinations
from collections import Counter
from math import comb

@lru_cache(None)
def matchings(n):
    if n==0:return ((),)
    out=[]
    for j in range(1,n,2):
        for l in matchings(j-1):
            for r in matchings(n-j-1):
                out.append(((0,j),)+tuple((a+1,b+1) for a,b in l)
                           +tuple((a+j+1,b+j+1) for a,b in r))
    return tuple(out)

def canonical(w):
    d={};out=[]
    for c in w:
        if c not in d:d[c]=len(d)
        out.append(d[c])
    return tuple(out)

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

def four_profile(k):
    n=2*k+2;counts=Counter()
    for m in matchings(n):
        for i,j in combinations(range(k+1),2):
            w=[None]*n
            for z,(a,b) in enumerate(m):
                label=i if z==j else z
                w[a]=w[b]=label
            counts[canonical(w)]+=1
    assert max(counts.values())<=2
    assert all(win(w) for w in counts)
    return counts

@lru_cache(None)
def noncrossing_blocks(n,t):
    if n==0:return ((),) if t==0 else ()
    if n<0 or t<0:return ()
    out=[]
    for size in (2,3):
        for end in combinations(range(1,n),size-1):
            pts=(0,)+end
            segments=list(zip([1]+[x+1 for x in end],list(end)+[n]))
            def recur(i,remaining,parts):
                if i==len(segments):
                    if remaining==0:out.append((pts,)+tuple(parts))
                    return
                st,en=segments[i]
                for u in range(remaining+1):
                    for sub in noncrossing_blocks(en-st,u):
                        moved=tuple(tuple(x+st for x in block) for block in sub)
                        recur(i+1,remaining-u,parts+list(moved))
            recur(0,t-(size==3),[])
    return tuple(out)

def two_triples_profile(k):
    n=2*k+2
    words=set()
    for blocks in noncrossing_blocks(n,2):
        w=[None]*n
        for i,b in enumerate(blocks):
            for p in b:w[p]=i
        words.add(canonical(w))
    assert all(win(w) for w in words)
    return words

if __name__=='__main__':
    for k in (5,6,7):
        four=four_profile(k)
        twice=sum(v==2 for v in four.values())
        assert twice==comb(2*k+2,k-1)
        print('FOUR',k,'patterns',len(four),'double_count',twice)
    k=7
    four=four_profile(k)
    triples=two_triples_profile(k)
    assert not set(four).intersection(triples)
    assert len(four)==32032 and len(triples)==24024
    print('SECOND DIAGONAL n=16,k=7:',len(four)+len(triples),
          'four',len(four),'two_triples',len(triples))

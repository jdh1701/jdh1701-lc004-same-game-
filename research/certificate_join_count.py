"""Experimental exact counting by joins of certificate constraints.
No novelty claim. Independent maximal-run comparison; no grammar oracle.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from check_partition_degree_encoding import partitions_with_sizes, noncrossing


def canonical(blocks, n):
    labels = [None]*n
    for j,b in enumerate(sorted(blocks)):
        for i in b: labels[i]=j
    return tuple(labels)


def join(p,q):
    parent=list(range(len(p)))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]; i=parent[i]
        return i
    for w in (p,q):
        first={}
        for i,a in enumerate(w):
            if a in first: parent[root(i)]=root(first[a])
            else: first[a]=i
    names={}
    return tuple(names.setdefault(root(i),len(names)) for i in range(len(p)))


def certificate_constraints(n):
    for t in range(n//3+1):
        if (n-3*t)%2: continue
        sizes=(2,)*((n-3*t)//2)+(3,)*t
        for blocks in partitions_with_sizes(tuple(range(n)),sizes):
            if noncrossing(blocks): yield canonical(blocks,n)


@lru_cache(None)
def stirling(n,k):
    if n==0:return int(k==0)
    if k==0:return 0
    return k*stirling(n-1,k)+stirling(n-1,k-1)


def join_coefficients(n):
    weights={}
    certificates=0
    for c in certificate_constraints(n):
        certificates+=1
        delta=defaultdict(int); delta[c]+=1
        for p,a in weights.items():delta[join(p,c)]-=a
        for p,a in delta.items():
            weights[p]=weights.get(p,0)+a
            if not weights[p]:del weights[p]
    return weights,certificates


@lru_cache(None)
def wins(w):
    if not w:return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2 and wins(w[:i]+w[j:]):return True
        i=j
    return False


def patterns(n):
    def rec(w,k):
        if len(w)==n:yield w,k
        else:
            for a in range(k+1):yield from rec(w+(a,),max(k,a+1))
    yield from rec((),0)


if __name__=='__main__':
    for n in range(0,10):
        weights,c=join_coefficients(n)
        predicted=[sum(a*stirling(len(set(p)),k) for p,a in weights.items()) for k in range(n+1)]
        actual=[0]*(n+1)
        for p,k in patterns(n):
            if wins(p):actual[k]+=1
        assert predicted==actual,(n,predicted,actual)
        # Stronger pointwise check of the signed union indicator.
        for p,k in patterns(n):
            score=sum(a for q,a in weights.items() if join(p,q)==p)
            assert score==int(wins(p)),(n,p,score)
        print('PASS',n,'certificates',c,'nonzero_join_terms',len(weights),'A',actual,flush=True)

"""Compute the exact falling-factorial coefficients of distinct words
accepted by the pair/triple Same Game grammar.

For length n, Q=floor(n/2) suffices because each new grammar production
contributes at least two positions. Prefixes use restricted-growth strings:
an existing color 0..k-1 or a single new color k. Each canonical word
represents (q)_k concrete color labelings. Deterministic parser-state sets
merge equivalent prefixes and count each accepted RGS word only once.

IMPORTANT: original maximal-run Same Game iff this grammar still requires
a general proof. Finite independent comparisons are not proof of that bridge.
"""
from collections import defaultdict
from functools import lru_cache
from time import perf_counter
S = -1

def coefficient_counts(Q,n,verbose=False):
    if Q<0 or n<0:raise ValueError((Q,n))
    @lru_cache(None)
    def closure(stacks, remain):
        out=set();work=list(stacks)
        while work:
            st=work.pop()
            if st in out or sum(c>=0 for c in st)>remain:continue
            out.add(st)
            if st and st[0]==S:
                tail=st[1:];work.append(tail)
                if remain>=2:
                    for a in range(Q):
                        work.append((a,S,a,S)+tail)
                        if remain>=3:work.append((a,S,a,S,a,S)+tail)
        return frozenset(out)
    current={(closure(frozenset({(S,)}),n),0):1}
    levels=[]
    for i in range(n):
        nxt=defaultdict(int)
        for (state,k),count in current.items():
            # One new-color possibility, regardless of how many unused
            # actual labels exist. Falling factorial restores their weight.
            for a in range(min(k+1,Q)):
                targets=frozenset(st[1:] for st in state if st and st[0]==a)
                if targets:
                    ns=closure(targets,n-i-1)
                    nxt[(ns,max(k,a+1))]+=count
        current=nxt;levels.append(len(current))
        if verbose:print(i+1,len(current),flush=True)
    coefficients=defaultdict(int)
    for (state,k),multiplicity in current.items():
        if () in state:coefficients[k]+=multiplicity
    return dict(sorted(coefficients.items())),levels,closure.cache_info().currsize

def falling(q,k):
    v=1
    for i in range(k):v*=q-i
    return v

def winning_polynomial_value(coefficients,q):
    return sum(c*falling(q,k) for k,c in coefficients.items())

if __name__=='__main__':
    for n in (8,10,12,13,14,15):
        t=perf_counter();coeff,lev,closures=coefficient_counts(n//2,n)
        print('n',n,'coefficients',coeff,'peak',max(lev),
              'closures',closures,'W3',winning_polynomial_value(coeff,3),
              'seconds',round(perf_counter()-t,3),flush=True)

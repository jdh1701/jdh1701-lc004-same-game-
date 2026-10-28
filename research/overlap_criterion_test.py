from functools import lru_cache
from itertools import combinations
from collections import defaultdict
from math import comb

@lru_cache(None)
def matchings(n):
    if n==0:return ((),)
    return tuple(((0,j),)+tuple((a+1,b+1) for a,b in L)
                 +tuple((a+j+1,b+j+1) for a,b in R)
                 for j in range(1,n,2)
                 for L in matchings(j-1)
                 for R in matchings(n-j-1))

def canonical(w):
    names={};out=[]
    for c in w:
        if c not in names:names[c]=len(names)
        out.append(names[c])
    return tuple(out)

def crosses(A,B):
    return any(a<b<c<d or b<a<d<c
               for a,c in combinations(A,2)
               for b,d in combinations(B,2))

def original_partition_noncrossing(w):
    blocks=defaultdict(list)
    for i,c in enumerate(w):blocks[c].append(i)
    groups=list(blocks.values())
    return all(not crosses(groups[i],groups[j])
               for i in range(len(groups))
               for j in range(i+1,len(groups)))

def check(k):
    multiplicities=defaultdict(int)
    for matching in matchings(2*k+2):
        for i,j in combinations(range(k+1),2):
            w=[None]*(2*k+2)
            for z,(a,b) in enumerate(matching):
                w[a]=w[b]=i if z==j else z
            multiplicities[canonical(w)]+=1
    failures=[(w,count) for w,count in multiplicities.items()
              if (count==2)!=original_partition_noncrossing(w)]
    assert not failures,failures[:2]
    assert max(multiplicities.values())==2
    double=sum(count==2 for count in multiplicities.values())
    assert double==comb(2*k+2,k-1)
    print('PASS',k,'distinct',len(multiplicities),'double',double,
          'matching_representations',sum(multiplicities.values()),flush=True)

if __name__=='__main__':
    for k in range(2,8):check(k)

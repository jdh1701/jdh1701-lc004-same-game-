"""Bit-mask separator complexes; preserve labels, joins and exact integer signs."""
from pathlib import Path
from functools import lru_cache
from itertools import combinations,product
from collections import defaultdict
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'research/ten_attacks_20261030'))
from core import catalogue,blocks

@lru_cache(None)
def local(n):
    out=[]
    for c in catalogue(n):
        bs=blocks(c);cuts=[]
        for m in range((1<<(len(bs)-1))-1):
            side=set(bs[0])
            for j,b in enumerate(bs[1:]):
                if m>>j&1:side.update(b)
            cuts.append(sum(1<<(i-1) for i in side if i))
        out.append((bs,tuple(cuts)))
    return out

def crosses(A,B):
    # Blocks are disjoint. Crossing iff one B point lies inside an A chord
    # and another outside. This is independent of the old four-loop test.
    if len(A)<2 or len(B)<2:return False
    for a,c in combinations(A,2):
        inside=sum(a<b<c for b in B)
        if 0<inside<len(B):return True
    return False

def maximal(fs):
    out=[]
    for f in sorted(set(fs),key=lambda f:(-f.bit_count(),f)):
        if not any(f&g==f for g in out):out.append(f)
    return tuple(sorted(out))

def encode(p):
    groups=blocks(p);localchoices=[local(len(g)) for g in groups]
    placed=[]
    for g,cs in zip(groups,localchoices):
        placed.append([tuple(tuple(g[i] for i in b) for b in bs) for bs,_ in cs])
    pair={}
    for i,j in combinations(range(len(groups)),2):
        pair[i,j]={(a,b) for a,A in enumerate(placed[i]) for b,B in enumerate(placed[j]) if not any(crosses(x,y) for x in A for y in B)}
    labels=sorted({(a,t) for a,cs in enumerate(localchoices) for _,cuts in cs for t in cuts})
    rank={v:i for i,v in enumerate(labels)}
    lf=[[sum(1<<rank[a,t] for t in cuts) for _,cuts in cs] for a,cs in enumerate(localchoices)]
    fs=[];choices=[];gencount=0;parent=list(range(len(p)))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    for inds in product(*(range(len(cs)) for cs in localchoices)):
        if any((inds[i],inds[j]) not in pair[i,j] for i,j in pair):continue
        gencount+=1;f=0
        for i,s in enumerate(inds):
            f|=lf[i][s]
            for b in placed[i][s]:
                for x in b[1:]:parent[root(x)]=root(b[0])
        fs.append(f);choices.append(inds)
    full=all(len({root(i) for i in g})==1 for g in groups)
    return dict(facets=maximal(fs),labels=labels,generators=gencount,full_join=full,choices=choices)

def bit_indices(v):
    while v:
        b=v&-v;yield b.bit_length()-1;v^=b

def strong(fs):
    fs=maximal(fs);trace=[]
    while fs:
        union=0
        for f in fs:union|=f
        support={v:sum(1<<i for i,f in enumerate(fs) if f>>v&1) for v in bit_indices(union)}
        pair=next(((v,w) for v,s in support.items() for w,t in support.items() if v!=w and s&t==s),None)
        if pair is None:break
        v,w=pair;trace.append((v,w));fs=maximal(f&~(1<<v) for f in fs)
    return fs,trace

@lru_cache(maxsize=100000)
def euler(fs):
    if not fs:return 0
    if fs==(0,):return 1
    common=fs[0];vs=0
    for f in fs:common&=f;vs|=f
    if common:return 0
    v=min(bit_indices(vs),key=lambda v:(abs(2*sum(f>>v&1 for f in fs)-len(fs)),v));b=1<<v
    return euler(maximal(f&~b for f in fs))-euler(maximal(f&~b for f in fs if f&b))

def faces(fs,cap=200000):
    out=set()
    for f in fs:
        s=f
        while True:
            out.add(s)
            if len(out)>cap:return None
            if not s:break
            s=(s-1)&f
    return out

def rank2(cols):
    basis={}
    for x in cols:
        while x:
            i=x.bit_length()-1
            if i in basis:x^=basis[i]
            else:basis[i]=x;break
    return len(basis)

def betti(F):
    dim=max((x.bit_count() for x in F),default=0)
    layers=[[s for s in F if s.bit_count()==k] for k in range(dim+1)]
    ranks=[0]*(dim+2)
    for k in range(1,dim+1):
        rows={s:i for i,s in enumerate(layers[k-1])}
        ranks[k]=rank2(sum(1<<rows[s^(1<<i)] for i in bit_indices(s)) for s in layers[k])
    return [len(ss)-ranks[k]-ranks[k+1] for k,ss in enumerate(layers)]

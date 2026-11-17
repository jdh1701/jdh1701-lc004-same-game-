import itertools
def parts(n):
    def rec(rem):
        if not rem: yield []; return
        f=rem[0]; rest=rem[1:]
        for sz in (2,3):
            for c in itertools.combinations(rest,sz-1):
                b=(f,)+c; r=[x for x in rest if x not in c]
                for p in rec(r): yield [b]+p
    for p in rec(list(range(n))):
        ok=all(not(a[0]<b[0]<a[-1]<b[-1]) or False for a in p for b in p if a is not b) if False else True
        lab={i:k for k,b in enumerate(p) for i in b}
        if all(not(lab[i]==lab[k] and lab[j]==lab[l] and lab[i]!=lab[j]) for i,j,k,l in itertools.combinations(range(n),4)): yield p
def join(n,p,q):
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for b in p+q:
        for i in b[1:]: par[f(i)]=f(b[0])
    g={}
    for i in range(n): g.setdefault(f(i),[]).append(i)
    return sorted(g.values())
n=8; P=list(parts(n)); best=None
for p in P:
    for q in P:
        x=join(n,p,q); lab={i:k for k,b in enumerate(x) for i in b}
        for i,j,k,l in itertools.combinations(range(n),4):
            if lab[i]==lab[k] and lab[j]==lab[l] and lab[i]!=lab[j]:
                m=min(len(x[lab[i]]),len(x[lab[j]]))
                if best is None or m<best[0]: best=(m,p,q,x)
print(best)

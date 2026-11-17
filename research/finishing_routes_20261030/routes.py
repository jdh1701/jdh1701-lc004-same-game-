"""Ten finishing attempts, with exact witnesses and explicit scope limits.

No floating point, unbounded search, or conjectural identities are used as proofs.
Run from the repository root. Large legacy inputs are hash-checked by restore_baseline.py.
"""
from pathlib import Path
from itertools import combinations, product
from fractions import Fraction
from collections import Counter
import hashlib, importlib.util, json, sys, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'research/fiber_elimination_20261030'))
from fast_complex import encode, local, maximal, faces, euler, crosses, bit_indices
from core import generators, join_value, join, blocks, two_patterns
spec=importlib.util.spec_from_file_location('choice_core',ROOT/'research/choice_complex_20261029/core.py')
cc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cc)

def save(name,data):
    (HERE/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    print(name, {k:v for k,v in data.items() if k not in ('rows','witness','coefficients','comparisons')},flush=True)

def conv(a,b,N):
    c=[0]*(N+1)
    for i,x in enumerate(a[:N+1]):
        for j,y in enumerate(b[:N+1-i]):c[i+j]+=x*y
    return c

def cumulants(m):
    N=len(m)-1;pows=[[1]+[0]*N]
    for k in range(N):pows.append(conv(pows[-1],m,N))
    c=[0]*(N+1)
    for n in range(1,N+1):c[n]=m[n]-sum(c[k]*pows[k][n-k] for k in range(1,n))
    return c

def moments(c):
    N=len(c)-1;m=[1]+[0]*N
    for n in range(1,N+1):
        power=[1]+[0]*n
        for k in range(1,n+1):
            power=conv(power,m,n)
            m[n]+=c[k]*power[n-k]
    return m

def interpolation():
    N=25;f=[0,1]
    for _ in range(N):f.append(sum(f[-2:]))
    m1=[1,0]+[1]*(N-1)
    m2=[1,0]+[2**n-2*n*f[n-2]-(-1)**n-1 for n in range(2,N+1)]
    m3=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503]
    c1,c2,c3=map(cumulants,(m1,m2,m3))
    assert moments(c1)==m1 and moments(c2)==m2 and moments(c3)==m3
    coeffs=[];pred=[0]*16
    for n in range(1,16):
        cubic=-35 if n==15 else 0
        a2=Fraction(c2[n]-2*c1[n]-6*cubic,2)
        a1=c1[n]-a2-cubic
        assert a1.denominator==a2.denominator==1
        assert n>=10 or a2==0
        pred[n]=int(3*a1+9*a2+27*cubic)
        assert pred[n]==c3[n]
        coeffs.append(dict(n=n,coefficients=[0,int(a1),int(a2),cubic]))
    assert moments(pred)==m3[:16]
    # This polynomial ambiguity is an information obstruction, not another game model.
    ambiguity=[b*(b-1)*(b-2) for b in range(4)]
    assert ambiguity==[0,0,0,6]
    mixed_cubic=Fraction(c3[16]-3*c2[16]+3*c1[16],6)
    save('02_interpolation',dict(status='VERIFIED-COMP',reconstructed_through=15,
        used_all_five_cubic_at_15=-35,mixed_cubic_at_16=int(mixed_cubic),
        ambiguity_at_b_0_1_2_3=ambiguity,coefficients=coeffs,
        moments= moments(pred),sources=['https://oeis.org/A035615','https://oeis.org/A035617'],
        conclusion='Support plus binary counts reconstructs through n14; the all-five n15 count extends to n15. Binary specialization alone cannot determine cubic terms at n16.'))

def matroid(rows):
    tried=0
    for r in rows:
        if not (3<=r['generators']<=12 and r['full_join']):continue
        p=tuple(r['p']);gs,_,_=generators(p);m=len(gs);basis=[];joins={0:tuple(range(len(p)))}
        for s in range(1,1<<m):
            bit=s&-s;joins[s]=join(joins[s^bit],gs[bit.bit_length()-1])
            if joins[s]==p and not any(b&s==b for b in basis):basis.append(s)
        tried+=1
        assert basis
        if len({b.bit_count() for b in basis})>1:
            save('03_matroid',dict(status='COUNTEREXAMPLE',patterns_checked=tried,witness=dict(p=p,generators=gs,bases=basis,basis_sizes=sorted({b.bit_count() for b in basis})),conclusion='Minimal top-joining certificate sets are not always matroid bases.'));return
        for a,b in product(basis,repeat=2):
            for x in bit_indices(a&~b):
                if not any((a^(1<<x)^(1<<y)) in basis for y in bit_indices(b&~a)):
                    save('03_matroid',dict(status='COUNTEREXAMPLE',patterns_checked=tried,witness=dict(p=p,generators=gs,bases=basis,exchange_failure=[a,b,x]),conclusion='Basis exchange fails.'));return
    save('03_matroid',dict(status='NO-COUNTEREXAMPLE-IN-SCOPE',patterns_checked=tried))

def flag(rows):
    tried=0
    for r in rows:
        if not r['full_join']:continue
        d=encode(tuple(r['p']));fs=d['facets'];V=sorted(set(v for f in fs for v in bit_indices(f)));tried+=1
        def face(s):return any(s&f==s for f in fs)
        for tri in combinations(V,3):
            t=sum(1<<v for v in tri)
            if not face(t) and all(face(t^(1<<v)) for v in tri):
                save('04_flag',dict(status='COUNTEREXAMPLE',patterns_checked=tried,witness=dict(p=r['p'],labels=d['labels'],facets=fs,missing_triangle=tri),conclusion='The separator complex is not determined by its one-skeleton.'));return
    save('04_flag',dict(status='NO-COUNTEREXAMPLE-IN-SCOPE',patterns_checked=tried))

def deletion(rows):
    witness=None;checked=0;fibers=0
    for r in rows:
        if sorted(r['profile']) not in ([5,6],[5,7]):continue
        p=tuple(r['p']);d=encode(p);groups=blocks(p)
        a=next(i for i,g in enumerate(groups) if len(g)==5);b=1-a
        # Project labelled separator facets after erasing the five-class vertices.
        remaining=encode(tuple(0 for _ in groups[b]));rank={t:i for i,(_,t) in enumerate(remaining['labels'])}
        projected=maximal(sum(1<<rank[t] for v,(cl,t) in enumerate(d['labels']) if cl==b and f>>v&1) for f in d['facets'])
        if witness is None and projected!=remaining['facets']:
            witness=dict(p=p,removed_class=a,projected_facets=projected,unrestricted_facets=remaining['facets'],labels=remaining['labels'])
        # Refined grammar: each fixed local certificate imposes exact crossing barriers.
        placed=[[tuple(tuple(g[i] for i in block) for block in bs) for bs,_ in local(len(g))] for g in groups]
        for i,A in enumerate(placed[a]):
            allowed={j for j,B in enumerate(placed[b]) if not any(crosses(x,y) for x in A for y in B)}
            actual={choice[b] for choice in d['choices'] if choice[a]==i}
            assert allowed==actual;fibers+=1
        checked+=1
    save('05_barrier_grammar',dict(status='VERIFIED-COMP',patterns_checked=checked,exact_fibers_checked=fibers,witness=witness,
        conclusion='Class deletion is not closed. Certificate-conditioned barrier rows are exact in this two-class census; no bounded barrier grammar is proved.'))

def charpoly(B):
    n=len(B);power=[[int(i==j) for j in range(n)] for i in range(n)];traces=[0];c=[1]
    for k in range(1,n+1):
        power=[[sum(power[i][u]*B[u][j] for u in range(n)) for j in range(n)] for i in range(n)]
        traces.append(sum(power[i][i] for i in range(n)))
        s=-sum(c[k-i]*traces[i] for i in range(1,k+1));assert s%k==0;c.append(s//k)
    return tuple(c)

def spectral(rows,output='06_gram_spectrum',profiles=([5,6],[5,7])):
    seen={};checked=0;witness=None
    for r in rows:
        if sorted(r['profile']) not in profiles:continue
        p=tuple(r['p']);d=encode(p);sizes=list(map(len,blocks(p)));a=min(range(2),key=lambda i:sizes[i]);b=1-a
        A=[[0]*len(local(sizes[b])) for _ in local(sizes[a])]
        for choice in d['choices']:A[choice[a]][choice[b]]=1
        B=[[sum(x*y for x,y in zip(row,col)) for col in A] for row in A]
        signature=(sizes[a],sizes[b],charpoly(B));checked+=1
        if signature in seen and seen[signature]['coefficient']!=r['coefficient'] and witness is None:
            witness=dict(first=seen[signature],second=dict(p=p,coefficient=r['coefficient'],matrix=A),gram_charpoly=signature[2])
        seen.setdefault(signature,dict(p=p,coefficient=r['coefficient'],matrix=A))
    save(output,dict(status='COUNTEREXAMPLE' if witness else 'NO-COUNTEREXAMPLE-IN-SCOPE',patterns_checked=checked,spectral_classes=len(seen),witness=witness,
        conclusion='Exact characteristic polynomials tested, without numerical eigenvalue tolerances.'))

def restrict(p,keep):return cc.canon(x for x in p if x in keep)
def raw_connected(groups):
    reach={0}
    while True:
        nxt=reach|{j for i in reach for j in range(len(groups)) if crosses(groups[i],groups[j])}
        if nxt==reach:return len(reach)==len(groups)
        reach=nxt

def allfive():
    source=ROOT/'research/scc_transfer_20261029/survivor_witnesses_25.txt'
    fixtures=[list(map(int,line.split())) for line in source.read_text().splitlines()]
    hereditary=None;shallow=None;checked=0;restrictions=0
    for row in fixtures:
        groups=[tuple(i for i in range(25) if m>>i&1) for m in row[:5]]
        choices,options=cc.atoms(groups)
        assert len(choices)==2 and all(x!=y for x,y in zip(*choices)) and raw_connected(groups)
        p=tuple(next(j for j,g in enumerate(groups) if i in g) for i in range(25));checked+=1
        certs=[tuple(B for g,c in enumerate(choice) for B in options[g][c]) for choice in choices]
        interval=[all(max(B)-min(B)+1==len(B) for B in cert) for cert in certs]
        if not any(interval) and shallow is None:shallow=dict(p=p,choices=choices,certificates=certs,interval_flags=interval)
        if hereditary is None:
            for keep in combinations(range(5),2):
                q=restrict(p,keep);qs=blocks(q)
                if not raw_connected(qs):continue
                cs,_=cc.atoms(qs);val=cc.coefficient(cs,2)[0];restrictions+=1
                if val==0:hereditary=dict(p=p,keep=keep,restriction=q,restriction_choices=cs,restriction_coefficient=val);break
        if hereditary is not None and shallow is not None:break
    save('07_hereditary_support',dict(status='COUNTEREXAMPLE' if hereditary else 'NO-COUNTEREXAMPLE-IN-SCOPE',survivors_checked=checked,connected_restrictions_checked=restrictions,witness=hereditary,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),conclusion='Tests heredity under deleting whole classes while retaining raw crossing connectivity.'))
    save('09_shallow_side',dict(status='HYPOTHESIS-FAILURE' if shallow else 'NO-COUNTEREXAMPLE-IN-SCOPE',survivors_checked=checked,witness=shallow,conclusion='The direct interval-partition hypothesis fails. This does not exclude an unknown transformation to shallow meanders.'))

def scc_route():
    pairs=0;intrinsic=0;failure=None
    for p in two_patterns(5,5):
        groups=blocks(p)
        if not raw_connected(groups):continue
        choices,options=cc.atoms(groups)
        for a,b in combinations(choices,2):
            if any(x==y for x,y in zip(a,b)):continue
            # edge i->j forbids the state b_i,a_j (bit_i=1,bit_j=0).
            k=len(groups);R=[[i==j for j in range(k)] for i in range(k)];edges=[]
            for i,j in product(range(k),repeat=2):
                if i!=j and any(crosses(x,y) for x in options[i][b[i]] for y in options[j][a[j]]):R[i][j]=True;edges.append([i,j])
            for t,i,j in product(range(k),repeat=3):R[i][j]|=R[i][t] and R[t][j]
            comps=[];seen=set()
            for i in range(k):
                if i not in seen:
                    comp=[j for j in range(k) if R[i][j] and R[j][i]];comps.append(comp);seen.update(comp)
            for comp in comps:
                if len(comp)<2:continue
                q=restrict(p,comp);cs,_=cc.atoms(blocks(q))
                assert len(cs)==2 and cc.coefficient(cs,len(comp))[0]==-1;intrinsic+=1
            pairs+=1
            unions=[tuple(sorted(x for i in comp for x in groups[i])) for comp in comps]
            if len(comps)>1 and any(crosses(A,B) for A,B in combinations(unions,2)) and failure is None:
                failure=dict(p=p,pair=[a,b],edges=edges,sccs=comps,coarsened_blocks=unions,all_choices=choices)
    save('08_scc_species',dict(status='COUNTEREXAMPLE' if failure else 'NO-COUNTEREXAMPLE-IN-SCOPE',separated_pairs_checked=pairs,nontrivial_intrinsic_components_checked=intrinsic,witness=failure,
        conclusion='SCC blocks need not form a noncrossing partition, obstructing the direct noncrossing species decomposition.'))

if __name__=='__main__':
    HERE.mkdir(exist_ok=True)
    rows=json.loads((ROOT/'research/ten_attacks_20261030/topology.json').read_text())['rows']
    start=time.monotonic()
    interpolation();matroid(rows);flag(rows);deletion(rows);spectral(rows);allfive();scc_route()
    holdout=json.loads((ROOT/'research/ten_attacks_20261030/holdout.json').read_text())['rows']
    spectral(rows+holdout,'06_gram_spectrum_holdout',([6,6],[6,7],[7,7]))
    print('elapsed',time.monotonic()-start,flush=True)

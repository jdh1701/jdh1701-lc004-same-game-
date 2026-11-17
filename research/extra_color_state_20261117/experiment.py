"""Pinned-table extra-base-color experiment. Right-top stack convention.

Two colors of the base are tracked, not its unbounded tail. On r=-1 a
new unknown predecessor is exposed. Keep BOTH proper possibilities there;
non-pop successors are determined by the stored color and a semantic witness.
No independence assumption and no sampled transition frequencies are used.
"""
import argparse, hashlib, itertools, json, pathlib, time
from functools import lru_cache
import numpy as np

ROOT=pathlib.Path(__file__).resolve().parents[1]/'entropy_certificate_20261111'
HERE=pathlib.Path(__file__).resolve().parent
PERMS=tuple(itertools.permutations('012'))

def fusion(S,a):
    out=set()
    for s in S:
        if s and s[-1]==a: out.update((s,s[:-1]))
        else: out.add(s+a)
    return out

def translate(s,p): return ''.join(p[int(c)] for c in s)

def build():
    lines=(ROOT/'prefix9-1.txt').read_text().splitlines()
    H,N=map(int,lines[0].split()); states=[]; edges=[]
    for i,line in enumerate(lines[1:]):
        f=line.split(); assert int(f[0])==i
        k=int(f[1]); states.append(tuple('' if s=='_' else s for s in f[2:2+k]))
        nums=list(map(int,f[2+k:])); edges.append(list(zip(nums[::2],nums[1::2])))
    assert len(states)==N
    J=np.zeros((N,2,3),dtype=np.int64); R=J.copy()
    K=np.zeros((2*N,3,2),dtype=np.int64); RR=np.zeros((2*N,3),dtype=np.int64)
    witnesses={}; pop=0; checks=0
    for i,S in enumerate(states):
        for b in (1,2):
            base=str(b)+'0'
            for a in range(3):
                j,r=edges[i][(b-1)*3+a]; assert r>=-1
                J[i,b-1,a]=j; R[i,b-1,a]=r
                actual=fusion((base+s for s in S),str(a)); L=2+r
                found=None
                for prefix in sorted({s[:L] for s in actual if len(s)>=L}):
                    for p in PERMS:
                        if p[0]!=prefix[-1]: continue
                        if {prefix+translate(s,p) for s in states[j]}<=actual:
                            found=(prefix,p); break
                    if found: break
                assert found is not None,(i,b,a)
                prefix,p=found; assert prefix[:1]==base[:1]
                inv={c:str(k) for k,c in enumerate(p)}
                if r==-1:
                    possible=tuple(sorted(int(inv[c]) for c in '012' if c!=str(b)))
                    assert possible==(1,2); pop+=1
                else:
                    possible=(int(inv[prefix[-2]]),)*2
                    assert possible[0] in (1,2)
                row=2*i+b-1; K[row,a]=[2*j+c-1 for c in possible]; RR[row,a]=r
                witnesses[i,b,a]=(j,r,prefix,p)
                # Independently check actual 3-letter bases: every possible older
                # color has a legal target, and its next b lies in the abstract edge.
                for c in '012':
                    if c==str(b): continue
                    B=c+base; B2=c+prefix
                    actual3=fusion((B+s for s in S),str(a))
                    assert {B2+translate(s,p) for s in states[j]}<=actual3
                    next_b=int(inv[B2[-2]])
                    assert 2*j+next_b-1 in K[row,a]; checks+=1
    return states,J,R,K,RR,witnesses,{'controls':N,'augmented_states':2*N,'edges':6*N,'pop_edges_with_unknown_older_color':pop,'determined_edges':6*N-pop,'three_letter_base_checks':checks}

def certificate_check(K,RR):
    out={}
    for name in ('tilted10-9.certificate.txt','refined-bias.certificate.txt'):
        rows=(ROOT/name).read_text().splitlines(); N,Q,hi,lo=map(int,rows[0].split())
        p=[]; fav=[]
        for row in rows[1:]:
            i,v,a,b=map(int,row.split()); p.extend((v,v)); fav.extend((a,b))
        # Python integers, not int64: refinement weights times Q can be large.
        worst=None
        for s in range(2*N):
            total=0
            for a in range(3):
                delta=int(RR[s,a])*Q+max(p[int(t)] for t in K[s,a])-p[s]
                total+=(hi if a==fav[s] else lo)*delta
            worst=total if worst is None else max(worst,total)
        assert worst<0
        out[name]={'maximum_drift_numerator':worst,'denominator':(hi+2*lo)*Q,'inequalities':2*N,'status':'PASS'}
    return out

def solve(J,R,K,RR,kind,iterations,tolerance):
    size=len(J) if kind=='old' else len(K)
    h=np.zeros(size); r=R if kind=='old' else RR
    def T(h):
        if kind=='old':return (r+h[J]).mean(2).max(1)
        return (r+h[K].max(2)).mean(1)
    start=time.time()
    for n in range(1,iterations+1):
        z=T(h); residual=z-h
        h=(h+z)/2; h-=h[0]
        if n%500==0: print(kind,n,float(residual.min()),float(residual.max()),flush=True)
        if residual.max()-residual.min()<tolerance:break
    Q=10**9; p=np.rint(h*Q).astype(np.int64)
    # For this bounded output the exact sum is safely below int64 range.
    assert np.max(np.abs(p))<10**14
    if kind=='old':nums=(R*Q+p[J]).sum(2).max(1)-3*p
    else:nums=(RR*Q+p[K].max(2)).sum(1)-3*p
    np.savetxt(HERE/(kind+'_potential.txt'),p,fmt='%d')
    return {'iterations':n,'seconds':time.time()-start,'residual_numerator_min':int(nums.min()),'residual_numerator_max':int(nums.max()),'denominator':3*Q,'lower':float(nums.min()/(3*Q)),'upper':float(nums.max()/(3*Q)),'interpretation':'Exact integer Bellman sub/supersolution bounds for THIS finite adversarial abstraction, not the real base process.'}

@lru_cache(None)
def raw_wins(w):
    if not w:return True
    i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2 and raw_wins(w[:i]+w[j:]):return True
        i=j
    return False

def small_cases(states,K,witnesses,limit):
    counts=[0]*(limit+1); counts[0]=1; checked=0; pop=0; boundary=0
    def visit(w,S,B,i,p):
        nonlocal checked,pop,boundary
        retained={B+translate(s,p) for s in states[i]}
        assert retained<=S
        assert ('' in S)==raw_wins(w)
        if len(w)==limit:return
        for a in '012':
            S2=fusion(S,a); inv={c:k for k,c in enumerate(p)}
            if len(B)<2:
                B2=min(fusion(retained,a)); j=0
                top=B2[-1] if B2 else '0'; p2=(top,*sorted(set('012')-{top}));boundary+=1
            else:
                b=inv[B[-2]]; aa=inv[a]; j,r,prefix,perm=witnesses[i,b,aa]
                B2=B[:-2]+translate(prefix,p); p2=tuple(p[int(c)] for c in perm)
                assert len(B2)==len(B)+r
                if len(B2)>=2:
                    b2=p2.index(B2[-2]); assert 2*j+b2-1 in K[2*i+b-1,aa]
                pop+=int(r==-1)
            checked+=1; counts[len(w)+1]+=int('' in S2)
            visit(w+a,S2,B2,j,p2)
    visit('',{''},'',0,tuple('012'))
    known=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385]
    assert counts==known[:limit+1]
    return {'max_length':limit,'prefix_transitions':checked,'exact_winning_counts':counts,'policy_pop_transitions':pop,'boundary_transitions':boundary,'status':'PASS','scope':'Exhaustive small words only; retained-policy acceptance is not exact recognition.'}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--iterations',type=int,default=12000); ap.add_argument('--small-n',type=int,default=9); args=ap.parse_args()
    assert 0<=args.small_n<=12
    states,J,R,K,RR,witnesses,meta=build();print('built',meta,flush=True)
    result={'source_commit':'0990b0e9a86a0adf78bdbf20a78bcceeafae4d39','model_sha256':hashlib.sha256((ROOT/'prefix9-1.txt').read_bytes()).hexdigest(),'model':meta,'inherited_certificates':certificate_check(K,RR),'small_cases':small_cases(states,K,witnesses,args.small_n)}
    print('checks',result,flush=True)
    for kind in ('old','extra_color'):result[kind]=solve(J,R,K,RR,kind,args.iterations,1e-10)
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
if __name__=='__main__':main()

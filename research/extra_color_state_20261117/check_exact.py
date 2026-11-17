"""Independent stdlib replay of uniform Bellman inequalities.

Reconstructs the lexicographic witness policy directly from the pinned table.
Uses arbitrary-size Python integers only. Never runs the optimizer or imports
experiment.py/NumPy. All extrema are computed, not accepted from results.json.
"""
import hashlib,itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parent
MODEL=D.parent/'entropy_certificate_20261111'/'prefix9-1.txt'
expected='9e2b870282b506b1e730d96faf57179cf54b719ee7d1b2cbebfb058cc37500cb'
assert hashlib.sha256(MODEL.read_bytes()).hexdigest()==expected
lines=MODEL.read_text().splitlines(); H,N=map(int,lines[0].split()); S=[]; E=[]
for i,line in enumerate(lines[1:]):
    f=line.split(); assert int(f[0])==i
    k=int(f[1]); S.append(tuple(() if x=='_' else tuple(map(int,x)) for x in f[2:2+k]))
    nums=list(map(int,f[2+k:])); E.append(list(zip(nums[::2],nums[1::2])))
assert len(S)==N
P=list(map(int,(D/'old_potential.txt').read_text().split()))
V=list(map(int,(D/'extra_color_potential.txt').read_text().split()))
assert len(P)==N and len(V)==2*N
Q=10**9; old=[]; new=[]; checks=0; pop=0
for i in range(N):
    old_options=[]
    for b in (1,2):
        old_total=0; new_total=0
        for a in range(3):
            j,r=E[i][3*(b-1)+a]; assert 0<=j<N and -1<=r<=H+1
            actual=set()
            for suffix in S[i]:
                stack=(b,0)+suffix
                if stack[-1]==a: actual.update((stack,stack[:-1]))
                else: actual.add(stack+(a,))
            L=2+r
            valid=[]
            for prefix in sorted({w[:L] for w in actual if len(w)>=L}):
                for p in itertools.permutations((0,1,2)):
                    if p[0]!=prefix[-1]:continue
                    if all(prefix+tuple(p[c] for c in w) in actual for w in S[j]):
                        valid.append((prefix,p))
            assert valid
            prefix,p=valid[0]; assert prefix[0]==b
            if r==-1:
                assert len(prefix)==1
                dest=[2*j+p.index(c)-1 for c in (0,1,2) if c!=b];pop+=1
            else:
                dest=[2*j+p.index(prefix[-2])-1]
            assert all(x in (2*j,2*j+1) for x in dest)
            old_total+=r*Q+P[j]
            new_total+=r*Q+max(V[x] for x in dest)
            checks+=1
        old_options.append(old_total-3*P[i])
        new.append(new_total-3*V[2*i+b-1])
    old.append(max(old_options))
assert min(old)>0 and min(new)>0
# Strictly disjoint bounds prove improvement for the selected finite models.
assert max(new)<min(old)
out={'status':'PASS','semantic_witnesses':checks,'pop_edges':pop,'scale':Q,
     'old_interval':{'numerators':[min(old),max(old)],'denominator':3*Q},
     'extra_color_interval':{'numerators':[min(new),max(new)],'denominator':3*Q},
     'both_lower_bounds_strictly_positive':True,'extra_color_upper_less_than_old_lower':True,
     'model_sha256':expected,
     'potential_sha256':{name:hashlib.sha256((D/name).read_bytes()).hexdigest() for name in ('old_potential.txt','extra_color_potential.txt')},
     'scope':'Finite max-adversary models with fixed lexicographic witnesses only; no impossibility claim about actual Same Game or other policies.'}
print(json.dumps(out,indent=2))

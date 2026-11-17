"""Independent tuple-based semantic/weighted audit, plus longer-base lifting tests.
No imports from the original checker or model generator. Python standard library.
"""
import hashlib, itertools, json, pathlib, sys
from fractions import Fraction
root=pathlib.Path(__file__).parent
raw=(root/'prefix9-1.txt').read_text().splitlines()
height,count=map(int,raw[0].split())
controls=[]; table=[]
for index,row in enumerate(raw[1:]):
    fields=row.split(); ident, size=map(int,fields[:2])
    assert ident==index and size>0
    suffixes=frozenset(() if s=='_' else tuple(map(int,s)) for s in fields[2:2+size])
    assert len(suffixes)==size
    for s in suffixes:
        assert len(s)<=height and all(c in (0,1,2) for c in s)
        assert not s or s[0]!=0
        assert all(s[k]!=s[k+1] for k in range(len(s)-1))
    assert len({s[0] if s else None for s in suffixes})>1 or suffixes=={()}
    nums=list(map(int,fields[2+size:]));assert len(nums)==12
    controls.append(suffixes);table.append(tuple(zip(nums[::2],nums[1::2])))
assert len(controls)==count and controls[0]=={()}
certificate=root/(sys.argv[1] if len(sys.argv)>1 else 'tilted10-9.certificate.txt')
cert=certificate.read_text().splitlines()
n,q,hi,lo=map(int,cert[0].split());assert n==count and q>0 and hi>lo>0
pot=[];fav=[]
for index,row in enumerate(cert[1:]):
    i,p,a,b=map(int,row.split());assert i==index and a in range(3) and b in range(3)
    pot.append(p);fav.append((a,b))
assert len(pot)==count and pot[0]==0
perms=tuple(itertools.permutations(range(3)))
bases=((1,0),(2,0),(0,1,0),(2,1,0),(0,2,0),(1,2,0))
checked=0; lifted=0; worst=None; absmax=0
for i,suffixes in enumerate(controls):
    for base in bases:
        row=(base[-2]-1)*3
        for color in range(3):
            reachable=set()
            for suffix in suffixes:
                stack=base+suffix
                if stack[-1]==color:
                    reachable.add(stack[:-1]);reachable.add(stack)
                else: reachable.add(stack+(color,))
            target,change=table[i][row+color]
            assert 0<=target<count and -1<=change<=height+1
            newsize=len(base)+change
            # Discover translated target sets from every real successor prefix,
            # not from the original checker's witness construction.
            ok=False
            for witness in reachable:
                prefix=witness[:newsize]
                if len(prefix)!=newsize or prefix[:len(base)-1]!=base[:-1]:continue
                for perm in perms:
                    if perm[0]!=prefix[-1]:continue
                    if all(prefix+tuple(perm[c] for c in suffix) in reachable
                           for suffix in controls[target]):
                        ok=True;break
                if ok:break
            assert ok,(i,base,color,target,change)
            checked+=1;lifted+=int(len(base)==3)
    for back in range(2):
        drift=Fraction(0)
        for color in range(3):
            j,change=table[i][3*back+color]
            step=Fraction(change)+Fraction(pot[j]-pot[i],q)
            absmax=max(absmax,abs(step))
            drift+=Fraction(hi if color==fav[i][back] else lo,hi+2*lo)*step
        assert drift<0,(i,back,drift)
        worst=drift if worst is None else max(worst,drift)
print(json.dumps({'status':'PASS','controls':count,'semantic_checks':checked,
 'extra_three_letter_base_checks':lifted,'rational_inequalities':2*count,
 'worst_drift':str(worst),'maximum_absolute_increment':str(absmax),
 'model_sha256':hashlib.sha256((root/'prefix9-1.txt').read_bytes()).hexdigest(),
 'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
 'scope':'Independent implementation on same certificate; longer-base finite tests are not a formal arbitrary-base proof.'},indent=2))

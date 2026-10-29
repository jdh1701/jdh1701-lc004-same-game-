import sys,time; sys.path.insert(0,'..')
from diag_formula import W
fn=sys.argv[1]; ok=bad=skip=0; t=time.time()
for line in open(fn):
    lhs,v=line.split('='); v=int(v)
    parts=[tuple(map(int,p.split(':'))) for p in lhs.split()]
    m2=sum(c for s,c in parts if s==2); m3=sum(c for s,c in parts if s==3)
    big=sorted([s for s,c in parts if s>=4 for _ in range(c)],reverse=True)
    if m2+m3==0: skip+=1; continue
    th=W(big,m2,m3)
    if th==v: ok+=1
    else: bad+=1; print("MISMATCH",lhs,v,th)
print(f"{fn}: profiles with rigid classes checked={ok+bad} pass={ok} fail={bad}; all-heavy profiles skipped={skip}; {time.time()-t:.0f}s")

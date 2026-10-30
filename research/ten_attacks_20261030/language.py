"""Attacks2--5: prime factorization, boundary rank, policies, run reliability."""
from core import *
import json,collections,time
HERE=Path(__file__).resolve().parent
start=time.time();out={}
#2 Positive free-monoid factorization into indecomposable winning words.
prime=[0]*10;counts=[0]*10;failure=None
for n in range(10):
    for w in product(range(3),repeat=n):
        if wins(w):
            counts[n]+=1
            if n and not any(wins(w[:j]) and wins(w[j:]) for j in range(1,n)):prime[n]+=1
free=[1]
for n in range(1,10):free.append(sum(prime[j]*free[n-j] for j in range(1,n+1)))
out['prime_factorization']=dict(distinct_winners=counts,indecomposables=prime,free_monoid_prediction=free,
    ambiguity_word=[0]*5,factorization_lengths=[[2,3],[3,2]])
assert free[:5]==counts[:5] and free[5]!=counts[5]
#3 An infinite identity submatrix: alternating shell with a two-cell center.
# This is accompanied by an all-m,n paper proof, not inferred from this check.
mat=[[int(wins((0,1)*m+(2,2)+(1,0)*n)) for n in range(31)] for m in range(31)]
assert mat==[[int(m==n) for n in range(31)] for m in range(31)]
out['boundary_rank']=dict(family='(01)^m 22 (10)^n',matrix_size=31,rank=31,identity=True)
#4 Eight candidate deterministic policies, first counterexample for each.
def moves(w):
    out=[];i=0
    while i<len(w):
        j=i+1
        while j<len(w) and w[j]==w[i]:j+=1
        if j-i>=2:out.append((i,j,w[:i]+w[j:]))
        i=j
    return out
policies={
'leftmost':lambda w,m:(-m[0],),
'rightmost':lambda w,m:(m[0],),
'longest_left':lambda w,m:(m[1]-m[0],-m[0]),
'shortest_left':lambda w,m:(m[0]-m[1],-m[0]),
'merge_first_left':lambda w,m:(int(0<m[0] and m[1]<len(w) and w[m[0]-1]==w[m[1]]),-m[0]),
'most_next_moves':lambda w,m:(len(moves(m[2])),-m[0]),
'fewest_next_runs':lambda w,m:(-sum(i==0 or m[2][i]!=m[2][i-1] for i in range(len(m[2]))),-m[0]),
'longest_next_run':lambda w,m:(max([b-a for a,b,_ in moves(m[2])]+[0]),-m[0])}
fails={}
for n in range(2,12):
    if len(fails)==len(policies):break
    for w in product(range(3),repeat=n):
        if not wins(w):continue
        ms=moves(w)
        for name,score in policies.items():
            if name in fails:continue
            move=max(ms,key=lambda m:score(w,m))
            if not wins(move[2]):fails[name]=dict(word=w,chosen_interval=move[:2],losing_successor=move[2],winning_intervals=[m[:2] for m in ms if wins(m[2])])
out['greedy_policies']=dict(test_through_length=n,policies=len(policies),failures=fails)
#5 Exact monotone run-template reliability. Normalize color names after moves.
def canon_state(s):
    d={};return tuple((d.setdefault(a,len(d)),h) for a,h in s)
@lru_cache(None)
def template_win(s):
    if not s:return True
    for i,(a,h) in enumerate(s):
        if not h:continue
        t=list(s[:i]+s[i+1:])
        if 0<i<len(s)-1 and s[i-1][0]==s[i+1][0]:t[i-1:i+1]=[(s[i-1][0],True)]
        if template_win(canon_state(t)):return True
    return False
T=collections.Counter();stats=[];hist_collision=None;by_hist={}
for r in range(1,10):
    maxprime=0;classes=0
    # all ternary proper skeletons modulo permutations of the three labels
    skeletons=[(0,)]
    for _ in range(r-1):skeletons=[p+(a,) for p in skeletons for a in range(min(3,max(p)+2)) if a!=p[-1]]
    for p in skeletons:
        good=[]
        for mask in range(1<<r):
            state=tuple((a,bool(mask>>i&1)) for i,a in enumerate(p))
            win=template_win(state)
            if r<=7:assert win==wins(tuple(a for a,h in state for _ in range(1+int(h))))
            if win:
                good.append(mask);k=len(set(p));weight=1
                for j in range(k):weight*=3-j
                T[r,mask.bit_count()]+=weight
        minimal=[m for m in good if all((m^(1<<i)) not in good for i in range(r) if m>>i&1)]
        maxprime=max(maxprime,len(minimal));classes+=1
        # Run count, turn count, and number of heavy runs are candidate aggregate states.
        turn=sum(p[i]!=p[i-2] for i in range(2,r))
        for mask in range(1<<r):
            sig=(r,turn,mask.bit_count())
            val=mask in good
            if hist_collision is None and sig in by_hist and by_hist[sig][2]!=val:
                hist_collision=dict(signature=sig,left=by_hist[sig],right=(p,mask,val))
            by_hist.setdefault(sig,(p,mask,val))
    stats.append(dict(runs=r,skeletons=classes,max_minimal_winning_heavy_sets=maxprime))
    print('templates',r,stats[-1],'seconds',round(time.time()-start,2),flush=True)
# A fixed r-run, h-heavy template contributes z^(r+h)/(1-z)^h.
import math
weighted=[1]+[sum(v*(int(n==r) if h==0 else (math.comb(n-r-1,h-1) if n>=r+h else 0)) for (r,h),v in T.items()) for n in range(1,10)]
assert weighted==counts
out['run_reliability']=dict(stats=stats,coefficients_through9=weighted,aggregate_counterexample=hist_collision,template_counts={str(k):v for k,v in T.items()})
(HERE/'language.json').write_text(json.dumps(out,indent=2)+'\n')
print('policies falsified',len(fails),'of',len(policies),'time',time.time()-start,flush=True)

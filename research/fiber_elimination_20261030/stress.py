from fast_complex import *
import argparse,json,time,signal
HERE=Path(__file__).resolve().parent;OLD=ROOT/'research/ten_attacks_20261030'
parser=argparse.ArgumentParser(description='Budgeted exact topology search; skips are not conclusions.')
parser.add_argument('--resume',action='store_true',help='Resume this script\'s partial checkpoint; otherwise start fresh.')
args=parser.parse_args()
start=time.time();controls=[]
# Cross-check every earlier exhaustive (5,6) pattern and all 32 skipped cases.
old=json.loads((OLD/'topology.json').read_text())['rows']
for r in old:
    if r['profile']!=[5,6]:continue
    d=encode(tuple(r['p']));fs,tr=strong(d['facets']);val=euler(fs)
    assert (d['generators'],d['full_join'],val)==(r['generators'],r['full_join'],r['coefficient'])
    controls.append(r['p'])
print('old controls',len(controls),'seconds',time.time()-start,flush=True)
prev=json.loads((HERE/"stress.partial.json").read_text()) if args.resume else dict(rows=[],counterexamples=[])
rows=prev["rows"];counter=prev["counterexamples"];done={tuple(r["p"]) for r in rows}
def check_inner(p,source):
    if p in done:return
    d=encode(p)
    if not d['full_join']:
        rows.append(dict(p=p,source=source,status='proper-join'));return
    fs,tr=strong(d['facets'])
    F=faces(fs,cap=30000)
    if F is None:
        rows.append(dict(p=p,source=source,status='SKIPPED-reduced-face-budget',generators=d['generators'],facets=len(fs)));return
    val=sum((-1)**f.bit_count() for f in F)
    h=betti(F) if val==0 and F is not None and len(F)<=3000 else None
    r=dict(p=p,source=source,status='evaluated',generators=d['generators'],coefficient=val,facets=len(fs),vertices=(sum(1 for _ in bit_indices(__import__('functools').reduce(int.__or__,fs,0)))),faces=len(F) if F is not None else None,homology=h)
    rows.append(r)
    if val==0 and h is not None and any(h):
        counter.append(dict(row=r,labels=d['labels'],facets=d['facets'],reduced_facets=fs,strong_trace=tr))
        print('COUNTEREXAMPLE',r,flush=True)
    if len(rows)%50==0:print('cases',len(rows),'seconds',time.time()-start,flush=True)
    (HERE/'stress.partial.json').write_text(json.dumps(dict(rows=rows,counterexamples=counter)))
class CaseTimeout(Exception):pass
signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(CaseTimeout()))
def check(p,source):
    if p in done:return
    signal.setitimer(signal.ITIMER_REAL,5)
    try:check_inner(p,source)
    except CaseTimeout:
        rows.append(dict(p=p,source=source,status='SKIPPED-five-second-case-budget'))
        print('case timeout',len(rows),source,flush=True)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        done.add(p)
        (HERE/'stress.partial.json').write_text(json.dumps(dict(rows=rows,counterexamples=counter)))
for r in json.loads((OLD/'deep_holdout.json').read_text())['rows']:
    if 'coefficient' not in r:check(tuple(r['p']),'old-budget-skip')

def comps(n,k):
    if k==1:yield (n,);return
    for a in range(1,n-k+2):
        for rest in comps(n-a,k-1):yield (a,)+rest
# Predeclared new six-run profiles, deduplicate only exact words.
for a,b in [(7,9),(8,10),(7,10),(6,11)]:
    for aa in comps(a,3):
        for bb in comps(b,3):
            p=tuple(x for i in range(3) for x in [0]*aa[i]+[1]*bb[i])
            check(p,f'all-six-run-{a}-{b}')
    print('profile complete',a,b,'counterexamples',len(counter),flush=True)
out=dict(status='VERIFIED-COMP',old_control_count=len(controls),rows=rows,counterexamples=counter,seconds_this_invocation=time.time()-start,budgets=dict(case_seconds=5,face_cap=30000,zero_homology_face_cap=3000),resumed=args.resume)
(HERE/'stress.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',len(rows),'counterexamples',len(counter),'seconds',time.time()-start,flush=True)

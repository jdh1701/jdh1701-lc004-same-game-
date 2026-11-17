"""Original maximal-run replay and targeted attacks on global closures."""
from pathlib import Path
from itertools import product
from collections import Counter
import json,sys,subprocess
from fusion import support,step,weighted,count,proper,weighted_totals
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research'))
from certificate_join_count import wins
stats=Counter();actual={}
for q,limit in [(2,12),(3,10),(4,7)]:
    counts=[]
    for n in range(limit+1):
        total=0
        for w in product(range(q),repeat=n):
            value=wins(w)
            assert (() in support(w))==value,(q,w)
            total+=value;stats['original_word_replays']+=1
            if q==3 and n<=7:
                for cut in range(n+1):
                    left=support(w[:cut]);right={s[::-1] for s in support(w[cut:])}
                    assert bool(left & right)==value
                    stats['split_intersection_checks']+=1
            if q==3 and n<=6:
                for t in support(w):
                    assert wins(w+t[::-1])
                    assert () in support(w+t[::-1])
                    stats['stack_separator_positive_checks']+=1
        counts.append(total)
    actual[q]=counts
# All proper prefix/suffix pairs give an exact exponentially large identity.
for m in range(1,6):
    words=[w for w in product(range(3),repeat=m) if proper(w)]
    assert len(words)==3*2**(m-1)
    for u in words:
        for v in words:
            assert wins(u+v[::-1])==(u==v)
            stats['proper_identity_entries']+=1
# Test ALL stack probes of bounded size, including absent support elements.
probes=[w for n in range(5) for w in product(range(3),repeat=n) if proper(w)]
for n in range(7):
    for w in product(range(3),repeat=n):
        S=support(w)
        for t in probes:
            assert wins(w+t[::-1])==(t in S)
            stats['stack_separator_all_checks']+=1
# Earliest ternary failure of reconstruction from the two-color projections.
projection_failure=None;checked=0
for n in range(11):
    for w in product(range(3),repeat=n):
        checked+=1
        pair_wins=all(wins(tuple(x for x in w if x!=a)) for a in range(3))
        if wins(w):assert pair_wins
        if pair_wins and not wins(w):projection_failure=w;break
    if projection_failure is not None:break
assert projection_failure is not None
# Independent explicit geometric witness used in the proof discussion.
fixed=(0,1,0,0,1,2,0,0,2)
assert not wins(fixed)
assert all(wins(tuple(x for x in fixed if x!=a)) for a in range(3))
radial=[]
for n in range(8):
    vals=[sum(wins(p+w) for w in product(range(3),repeat=n)) for p in [(0,1,0),(0,1,2)]]
    radial.append(vals)
assert radial[-1]==[131,132] and all(a==b for a,b in radial[:-1])
# Scalar trace overcounts witnesses already on four equal letters.
assert weighted((0,0,0,0))[()]==2 and wins((0,0,0,0))
for n in range(9):
    witness_sum=0
    for w in product(range(3),repeat=n):
        reference=support(w)
        for parameter in [1,2,3]:
            assert set(weighted(w,parameter))==set(reference)
            stats['positive_parameter_support_checks']+=1
        witness_sum+=weighted(w).get((),0)
    assert witness_sum==weighted_totals(3,8)[n]
# Python/C++ agreement on full state-level counts, not just final totals.
binary=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/tmp/lc004-fusion-count')
cpp=[]
known=[1,0,3,3,15,33,105,297,879,2631,7833,23697,71385,216765,657849,2003151,6103743,18624693,56870385,173760513,531128349,1623881889,4965695331,15185222199,46435889601,141985777503]
for n in range(19):
    proc=subprocess.run([str(binary),str(n),'2000000'],check=True,capture_output=True,text=True)
    row=json.loads(proc.stdout);assert row['status']=='complete' and row['count']==known[n]
    if n<=14:
        py,levels=count(3,n)
        assert py==row['count'] and levels==row['states']
        stats['python_cpp_full_state_level_replays']+=1
    cpp.append(row)
result={'status':'VERIFIED-COMP','statistics':dict(stats),'direct_counts':actual,
 'first_binary_projection_failure':{'word':projection_failure,'length':len(projection_failure),'words_examined':checked,'all_shorter_words_exhausted':True},
 'explicit_projection_witness':fixed,'radial_prefixes':[(0,1,0),(0,1,2)],'radial_continuation_counts':radial,
 'witness_multiplicity_counterexample':{'word':[0,0,0,0],'coefficient':2,'winning_indicator':1},
 'scalar_witness_totals':weighted_totals(3,18),'cpp_replays':cpp,
 'scope':'Exact finite checks of the global support bridge and failed counting closures; no all-length scalar formula or polynomial state bound.'}
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cpp_replays','direct_counts')},indent=2))

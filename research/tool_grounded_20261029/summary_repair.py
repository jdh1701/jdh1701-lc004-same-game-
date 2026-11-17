"""Bounded synthesis with a frozen training length and a held-out length.

The SMT task selects ordered heaviness flags sufficient for observed
one-cell continuations. The claimed result is only the finite experiment.
"""
from pathlib import Path
from itertools import combinations
from collections import defaultdict
import json,sys
from z3 import Bool, Optimize, Solver, Or, Sum, If, sat, unsat
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from heavy_greedy_obstruction import heavy_patterns, bfs
from rigid_face_geometry_check import wins

ROOT=Path(__file__).resolve().parent


def describe(word):
    runs=[]
    for a in word:
        if runs and runs[-1][0]==a:
            runs[-1][1]+=1
        else:
            runs.append([a,1])
    summary=(tuple(word.count(a) for a in range(3)),tuple(a for a,n in runs),
             runs[0][1],runs[-1][1],sum(n>=2 for a,n in runs))
    return summary,tuple(n>=2 for a,n in runs)


def dataset(n):
    groups=defaultdict(list);inputs=0
    for word in heavy_patterns(n):
        if len(set(word))!=3:
            continue
        inputs+=1
        summary,bits=describe(word)
        if any(summary[1].count(a)<2 for a in range(3)):
            continue
        if any(set(word[:i]).isdisjoint(word[i:]) for i in range(1,n)):
            continue
        if wins(word):
            continue
        future=tuple(wins(word+(a,)) for a in range(3))
        groups[summary].append((word,bits,future))
    return groups,inputs


def differences(groups):
    constraints=set();witness=None
    for group in groups.values():
        for left,right in combinations(group,2):
            if left[2]==right[2]:
                continue
            bits=frozenset(i for i,(a,b) in enumerate(zip(left[1],right[1])) if a!=b)
            assert bits, 'Exact encoded state must determine continuations'
            constraints.add(bits)
            if witness is None:
                suffix=next(i for i,(a,b) in enumerate(zip(left[2],right[2])) if a!=b)
                witness=dict(left=left[0],right=right[0],suffix=suffix,
                             left_wins=left[2][suffix],right_wins=right[2][suffix])
    return constraints,witness


def sufficient(selected,constraints):
    return all(set(selected)&set(c) for c in constraints)


def run():
    train,inputs=dataset(12)
    constraints,witness=differences(train)
    positions=range(12);keep=[Bool('keep_'+str(i)) for i in positions]
    clauses=[Or([keep[i] for i in c]) for c in sorted(constraints,key=lambda x:sorted(x))]
    cost=Sum([If(v,1,0) for v in keep])
    opt=Optimize();opt.set(timeout=20000);opt.add(*clauses);opt.minimize(cost)
    assert opt.check()==sat
    model=opt.model();selected=[i for i in positions if bool(model.eval(keep[i],model_completion=True))]
    assert sufficient(selected,constraints)
    lower=Solver();lower.set(timeout=20000);lower.add(*clauses,cost<len(selected))
    assert lower.check()==unsat, 'Optimality must be checked, not inferred from timeout'
    # Separate exhaustive verifier: no SMT and no symbolic optimizer.
    for k in range(len(selected)):
        assert not any(sufficient(c,constraints) for c in combinations(positions,k))
    heldout,test_inputs=dataset(13)
    test_constraints,_=differences(heldout)
    failure=None
    for group in heldout.values():
        fingerprints={}
        for word,bits,future in group:
            key=tuple(bits[i] if i<len(bits) else False for i in selected)
            if key in fingerprints and fingerprints[key][2]!=future:
                old=fingerprints[key]
                suffix=next(i for i,(a,b) in enumerate(zip(old[2],future)) if a!=b)
                failure=dict(left=old[0],right=word,suffix=suffix,
                             left_wins=old[2][suffix],right_wins=future[suffix]);break
            fingerprints[key]=(word,bits,future)
        if failure:
            break
    for example in [witness,failure]:
        if example is None:
            continue
        a,b=tuple(example['left']),tuple(example['right']);suffix=(example['suffix'],)
        assert describe(a)[0]==describe(b)[0]
        assert not bfs(a)[0] and not bfs(b)[0]
        assert bfs(a+suffix)[0]==example['left_wins']
        assert bfs(b+suffix)[0]==example['right_wins']
    return dict(training_length=12,training_ternary_heavy_patterns=inputs,
                distinct_constraints=len(constraints),selected_run_positions=selected,
                minimum_retained_positions=len(selected),minimum_independently_checked=True,
                heldout_length=13,heldout_ternary_heavy_patterns=test_inputs,
                survives_heldout=sufficient(selected,test_constraints),
                witness=witness,heldout_counterexample=failure,
                scope='One-letter continuations of losing, indecomposable, ternary-heavy canonical patterns; each color occupies at least two runs',
                assurance='Finite synthesis and held-out testing; no universal compact-state theorem')


if __name__=='__main__':
    result=run();(ROOT/'summary-repair-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

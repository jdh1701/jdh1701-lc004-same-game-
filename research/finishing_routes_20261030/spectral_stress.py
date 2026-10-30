"""Adversarial continuation of route 6, seeded and with a visible finite scope."""
from routes import *
import random
rng=random.Random(20261030);seen={};checked=0;collisions=0;witness=None;counts=Counter()
inputs=[]
for name in ('topology','holdout','deep_holdout'):
    for r in json.loads((ROOT/'research/ten_attacks_20261030'/(name+'.json')).read_text())['rows']:
        if len(r['profile'])==2 and 'coefficient' in r:inputs.append((tuple(r['p']),r['coefficient']))
for profile in ((6,8),(6,9),(7,8),(7,9),(8,8)):
    patterns=list(two_patterns(*profile));rng.shuffle(patterns)
    inputs.extend((p,None) for p in patterns[:500])
used=set();start=time.monotonic()
for p,known in inputs:
    if p in used:continue
    used.add(p);groups=blocks(p);sizes=list(map(len,groups));a=min(range(2),key=lambda i:sizes[i]);b=1-a
    d=encode(p);value=euler(d['facets']) if d['generators'] else 0
    if known is not None:assert value==known
    A=[[0]*len(local(sizes[b])) for _ in local(sizes[a])]
    for choice in d['choices']:A[choice[a]][choice[b]]=1
    B=[[sum(x*y for x,y in zip(row,col)) for col in A] for row in A]
    # Necessary spectral invariants filter pairs before full characteristic polynomials.
    tr1=sum(B[i][i] for i in range(len(B)))
    tr2=sum(x*x for row in B for x in row)
    signature=(sizes[a],sizes[b],tr1,tr2)
    for old in seen.get(signature,[]):
        if old['coefficient']==value:continue
        collisions+=1
        if charpoly(B)==charpoly(old['gram']):
            witness=dict(first={k:v for k,v in old.items() if k!='gram'},second=dict(p=p,coefficient=value,matrix=A),gram_charpoly=charpoly(B));break
    seen.setdefault(signature,[]).append(dict(p=p,coefficient=value,matrix=A,gram=B));checked+=1;counts[str(sorted(sizes))]+=1
    if checked%500==0:print('checked',checked,'full_charpoly_comparisons',collisions,flush=True)
    if witness:break
save('06_gram_spectrum_stress',dict(status='COUNTEREXAMPLE' if witness else 'NO-COUNTEREXAMPLE-IN-SCOPE',seed=20261030,patterns_checked=checked,profiles=dict(counts),full_charpoly_comparisons=collisions,witness=witness,seconds=time.monotonic()-start,conclusion='A finite spectral test, not a spectral formula or universal invariance theorem.'))

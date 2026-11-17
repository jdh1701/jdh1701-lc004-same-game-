"""Self-contained certificate audit. Python standard library only; no optimizer.

Usage: python3 audit_certificate.py prefix9-1.txt tilted10-9.certificate.txt
Stack top is on the RIGHT. This checks a conservative support policy, not counts.
"""
from pathlib import Path
from itertools import permutations
import hashlib, json, math, sys

model, certificate = map(Path, sys.argv[1:3])
lines = model.read_text().splitlines()
H, N = map(int, lines[0].split())
states, edges = [], []
for line in lines[1:]:
    t = line.split(); i, k = map(int, t[:2])
    assert i == len(states) and k > 0
    words = tuple('' if w == '_' else w for w in t[2:2+k])
    assert len(words) == len(set(words)) == k
    assert all(set(w) <= set('012') and len(w) <= H for w in words)
    assert all(not w or w[0] != '0' for w in words)
    assert all(all(x != y for x, y in zip(w, w[1:])) for w in words)
    assert not words[0] or any(not w or w[0] != words[0][0] for w in words)
    v = list(map(int, t[2+k:])); assert len(v) == 12
    states.append(words); edges.append(list(zip(v[::2], v[1::2])))
assert len(states) == N and states[0] == ('',)

rows = certificate.read_text().splitlines()
n, scale, high, low = map(int, rows[0].split())
assert n == N and scale > 0 and high > low > 0
potential, favorites = [], []
for line in rows[1:]:
    i, p, a, b = map(int, line.split())
    assert i == len(potential) and a in range(3) and b in range(3)
    potential.append(p); favorites.append((a,b))
assert len(potential) == N and potential[0] == 0

worst, max_abs, semantic_edges = None, 0, 0
for i, words in enumerate(states):
    for b in (0,1):
        base = str(b+1)+'0'
        weighted = 0
        for a in range(3):
            color = str(a)
            actual = set()
            for suffix in words:
                stack = base+suffix
                if stack[-1] == color:
                    actual.update((stack,stack[:-1]))
                else:
                    actual.add(stack+color)
            j, r = edges[i][b*3+a]
            assert j in range(N) and -1 <= r <= H+1
            length = len(base)+r
            # Find a concrete new base and inverse relabeling whose entire
            # target set is contained in the real one-letter successor set.
            prefixes = {s[:length] for s in actual if len(s) >= length}
            witness = False
            for prefix in sorted(prefixes):
                assert prefix[:len(base)-1] == base[:-1]
                others = sorted(set('012')-{prefix[-1]})
                for x,y in permutations(others):
                    mapping = {'0':prefix[-1], '1':x, '2':y}
                    lifted = {prefix+''.join(mapping[c] for c in w) for w in states[j]}
                    if lifted <= actual:
                        witness = True
                        break
                if witness: break
            assert witness, (i,b,a,j,r)
            semantic_edges += 1
            delta = r*scale+potential[j]-potential[i]
            max_abs = max(max_abs,abs(delta))
            weighted += (high if a == favorites[i][b] else low)*delta
        worst = weighted if worst is None else max(worst,weighted)
assert worst is not None and worst < 0, ('no strict negative certificate',worst)
den = high+2*low
print(json.dumps({
    'status':'PASS', 'states':N, 'suffix_height':H,
    'semantic_edges_checked':semantic_edges, 'integer_inequalities_checked':2*N,
    'scale':scale, 'weights':[high,low,low], 'weight_denominator':den,
    'max_drift_numerator':worst, 'drift_denominator':den*scale,
    'max_absolute_increment_numerator':max_abs,
    'potential_extrema_numerators':[min(potential),max(potential)],
    'growth_expression':f'{den}/({high}^{high}*{low}^{2*low})^(1/{den})',
    'growth_decimal_display_only':math.exp(math.log(den)-(high*math.log(high)+2*low*math.log(low))/den),
    'model_sha256':hashlib.sha256(model.read_bytes()).hexdigest(),
    'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
    'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'no_optimizer_or_third_party_packages':True,
    'scope':'Finite semantic and integer checks; probability argument is a paper proof, not Lean.'
},indent=2))

# A general inflation correction formula

2026-10-31. PROVED-PAPER by the finite join-algebra reduction below. This
supplement is not a Lean theorem. Its 15-type algebra check and 297 finite
pattern tests ran locally after the pinned proof source was frozen; they are
not represented as part of that source's hosted computational checks.

Let p be any all-five pattern with a designated adjacent equal pair, and let
p+ duplicate a point between that pair. Let F be the COMPLETE original
noncrossing 2/3 certificate family refining p. Define

    T = {c in F : the designated pair lies in a three-point block of c},
    kappa_T(p) = sum over nonempty S subset T with join S = p of (-1)^(|S|+1).

The subscript matters: this is the restricted original signed-join sum, not
necessarily the winning coefficient of another game pattern.

If p is NCConnected and has at least two classes, then

    kappa(p+) = kappa(p) - 2*kappa_T(p).

Thus arbitrary-family inflation preservation reduces to the specific
cancellation claim kappa_T(p)=0. That cancellation remains OPEN. This identity
does not solve enumeration of the exceptional first-excess families.

For disconnected patterns a correction is necessary:

    kappa(p+) = kappa(p) - 2*kappa_T(p) + gamma_U.

Here gamma_U is the signed-join coefficient, at the restricted outside pattern,
of the complete OUTSIDE configurations whose every block stays in a single
gap of the distinguished five-class. The four gaps exclude the empty gap
between the designated adjacent positions. These outside configurations allow
all five choices for the distinguished class. gamma_U may be nonzero; it is
not silently dropped in the finite tests.

## Proof

Use the actual-position gap reduction in REPORT.md. For a fixed feasible
outside configuration x, let S_x be the permitted old local states. The chord
table in Lean catalogue order, for two distinct gap indices g<h, is:

| g,h | Permitted old states |
|---|---|
| 0,1 | empty |
| 0,2 | {1} |
| 0,3 | {2} |
| 1,2 | empty |
| 1,3 | {0} |
| 2,3 | empty |

Two endpoints in the same gap permit all five states. Intersecting these
constraints over all outside blocks shows that S_x is empty, one of {0},{1},
{2}, or the entire five-state catalogue. Empty cases contribute no generators
and are discarded. Call the four nonempty types A,B,C,U respectively.
Under inflation their local sets become {2,4}, {3,6}, {0}, and all eight
six-state choices, exactly as in the previously checked replacement table.
Restriction to T changes the old sets to {0},{1},empty,{0,1}.

Work in the integral algebra with one basis symbol E_r for each local
partition r, and multiplication E_r E_s = E_(r join s). Its unit is the
discrete partition, and every basis element is idempotent. For any local
generator set S put

    U(S) = 1 - product_(s in S) (1 - E_s).

All factors commute; (1-E_s)^2=(1-E_s), so U(S)^2=U(S). Consequently products
of such elements depend only on which of the four types occur, not on how
often a type occurs.

For an outside configuration x let Z_x be its outside partition symbol.
Idempotence of Z_x gives the exact grouping identity

    product_(s in S_x)(1-Z_x E_s) = 1-Z_x U(S_x).

The winning-union polynomial is therefore

    1 - product_x(1-Z_x U(S_x))
      = sum_(nonempty X) (-1)^(|X|+1) Z_(join X) product_(x in X) U(S_x).

This identity groups the original signed certificate subsets without dropping
duplicates or assuming uniform signs. The desired coefficient is the
coefficient of the full distinguished class AND the full outside pattern.
The same expansion applies to the inflated family and to T.

For each nonempty type set I, write O(I), N(I), R(I) for the coefficient of
the full local class in the old, new, and restricted products. The complete
finite join calculation is below; bit values A=1, B=2, C=4, U=8 identify I.

| I | O(I) | N(I) | R(I) | 1 if I={U}, else 0 |
|---:|---:|---:|---:|---:|
| 1 | 0 | 0 | 0 | 0 |
| 2 | 0 | 0 | 0 | 0 |
| 3 | 1 | -1 | 1 | 0 |
| 4 | 0 | 0 | 0 | 0 |
| 5 | 1 | 1 | 0 | 0 |
| 6 | 1 | 1 | 0 | 0 |
| 7 | 1 | 1 | 0 | 0 |
| 8 | -4 | -1 | -1 | 1 |
| 9 | 0 | 0 | 0 | 0 |
| 10 | 0 | 0 | 0 | 0 |
| 11 | 1 | -1 | 1 | 0 |
| 12 | 0 | 0 | 0 | 0 |
| 13 | 1 | 1 | 0 | 0 |
| 14 | 1 | 1 | 0 | 0 |
| 15 | 1 | 1 | 0 | 0 |

Every row satisfies N=O-2R+1_(I={U}). Multiplying by the unchanged outside
coefficient and summing over X proves the general formula including gamma_U.
Repeated type occurrences cause no additional cases by the proved
idempotence. This is a finite algebra proof of an unbounded identity, rather
than an inference from the sampled patterns.

It remains to justify gamma_U=0 in the connected case. The existing
NCConnected-every-class-crossed theorem supplies another class with points in
at least two gaps of the distinguished class. Every universal outside
configuration preserves the gap partition: each of its blocks lies in a
single gap, as the chord table shows. Every join of such configurations still
preserves the gaps. It therefore cannot connect all points of that crossed
outside class. No subset contributes to the full outside pattern, and
gamma_U=0. This completes the connected identity.

As a check, for a single five-class the old coefficient is -4, the restricted
two-generator coefficient is -1, and gamma_U=1. The formula gives -1 for the
inflated single six-class, matching the existing verified evaluation. The
connected specialization is not applied to this one-class example.

## Reproduce the finite algebra table

Run from the repository root. Python's catalogue ordering differs from Lean's;
the indices below follow the original-block Python catalogue explicitly.

```python
import sys
from collections import defaultdict
sys.path.insert(0, 'research/ten_attacks_20261030')
from core import catalogue, join
cs = {5: catalogue(5), 6: catalogue(6)}

def U(n, inds):
    d = {}
    for i in inds:
        q = cs[n][i]
        delta = defaultdict(int)
        delta[q] += 1
        for p, v in d.items():
            delta[join(p, q)] -= v
        for p, v in delta.items():
            d[p] = d.get(p, 0) + v
    return {p:v for p,v in d.items() if v}

def top_coefficient(n, ops):
    d = {tuple(range(n)): 1}
    for op in ops:
        e = defaultdict(int)
        for p,v in d.items():
            for q,w in op.items():
                e[join(p,q)] += v*w
        d = {p:v for p,v in e.items() if v}
    return d.get((0,)*n, 0)

old = [U(5,[2]), U(5,[3]), U(5,[0]), U(5,range(5))]
new = [U(6,[0,2]), U(6,[1,3]), U(6,[5]), U(6,range(8))]
restricted = [U(5,[2]), U(5,[3]), {}, U(5,[2,3])]
for mask in range(1,16):
    inds = [i for i in range(4) if mask>>i&1]
    o = top_coefficient(5, [old[i] for i in inds])
    n = top_coefficient(6, [new[i] for i in inds])
    r = top_coefficient(5, [restricted[i] for i in inds])
    correction = int(mask == 8)
    assert n == o - 2*r + correction
    print(mask, o, n, r, correction)
```

## Additional original-position checks

The following finite probe passed 297 tests: one at length5, all56 two-class
patterns with the chosen adjacent pair fixed at positions0,1, and80 seeded
random balanced patterns at each of lengths15,20,25. Tests may repeat patterns;
this is not 297 distinct patterns or an independent full census. Five cases
have a nonzero universal correction and five have a nonzero restricted term.
Many random cases have no certificates, so these probes add less evidence
than the complete local algebra proof. The probe shares existing catalogue
and Euler utilities and is not described as wholly independent.

```python
import sys, random
sys.path.insert(0, 'research/fiber_elimination_20261030')
from fast_complex import encode, euler, maximal, local
from core import two_patterns
random.seed(310610)

def restricted_value(d, universal=False):
    labels = [x for x in d['labels'] if not universal or x[0] != 0]
    rank = {x:i for i,x in enumerate(labels)}
    fs = []
    for c in d['choices']:
        if c[0] not in ((1,4) if universal else (2,3)):
            continue
        mask = 0
        for a,s in enumerate(c):
            if universal and a == 0:
                continue
            for t in local(5)[s][1]:
                mask |= 1 << rank[a,t]
        fs.append(mask)
    return euler(maximal(fs))

patterns = [(0,)*5]
patterns += [p for p in two_patterns(5,5) if p[0] == p[1]]
for j in (3,4,5):
    for _ in range(80):
        tail = [0]*3 + [a for a in range(1,j) for _ in range(5)]
        random.shuffle(tail)
        patterns.append((0,0)+tuple(tail))
for p in patterns:
    d = encode(p)
    old = euler(d['facets'])
    restricted = restricted_value(d)
    universal = restricted_value(d, True)
    new = euler(encode(p[:1]+(0,)+p[1:])['facets'])
    assert new == old - 2*restricted + universal
assert len(patterns) == 297
print('297 finite checks passed')
```

The next mathematical target is the vanishing of the restricted term for
connected all-five patterns. It remains conjectural. Neither this formula
nor its finite probes establish that vanishing or an all-length count.

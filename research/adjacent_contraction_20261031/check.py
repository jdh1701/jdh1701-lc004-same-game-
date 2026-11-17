"""Original-position checks; no assumed survivor classification or sign rule."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import random
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'research/fiber_elimination_20261030'))
from fast_complex import encode, euler, local
from core import blocks, canonical, crossing, generators, join, join_value


def norm(p):
    seen = {}
    return tuple(seen.setdefault(x, len(seen)) for x in p)


def duplicate(p):
    return norm(p[:1] + p)


def contract(p):
    return norm(p[1:])


def original_certificates(p, data):
    groups = blocks(p)
    return tuple(canonical([tuple(g[i] for i in b)
                            for g, s in zip(groups, choice)
                            for b in local(len(g))[s][0]], len(p))
                 for choice in data['choices'])


def connected(p):
    # Compute the least noncrossing coarsening by merging crossed classes.
    while True:
        bs = blocks(p)
        merged = False
        for a, b in combinations(bs, 2):
            if crossing(a, b):
                ca, cb = p[a[0]], p[b[0]]
                p = norm(tuple(ca if x == cb else x for x in p))
                merged = True
                break
        if not merged:
            return len(set(p)) == 1


def patterns(profile):
    # Distinguished class has five points and contains positions 0 and 1.
    # Quotient out repeated sizes only among the nondistinguished classes.
    n = sum(profile)
    def fill(rest, sizes, used):
        if not sizes:
            p = [-1] * n
            for a, bs in enumerate(used):
                for i in bs:
                    p[i] = a
            yield tuple(p)
            return
        for chosen in combinations(rest, sizes[0]):
            if len(used) > 1 and profile[len(used)-1] == sizes[0]:
                if min(chosen) < min(used[-1]):
                    continue
            s = set(chosen)
            yield from fill(tuple(i for i in rest if i not in s),
                            sizes[1:], used + [chosen])
    for tail in combinations(range(2, n), 3):
        a = (0, 1) + tail
        yield from fill(tuple(i for i in range(n) if i not in a), profile[1:], [a])


counts = Counter()
profiles = {}
nonzero_examples = []


def check(p, independent=False):
    p = norm(p)
    assert p[0] == p[1] == 0 and p.count(0) == 5
    q = contract(p)
    inflated = norm(p[:1] + (0,) + p[1:])
    dp, dq, di = encode(p), encode(q), encode(inflated)
    cs = original_certificates(p, dp)
    ds = original_certificates(q, dq)
    restricted = tuple(c for c in cs if c[0] == c[1] and c.count(c[0]) == 3)
    assert len(cs) == len(set(cs)) and len(ds) == len(set(ds))
    assert len(restricted) == len(ds)
    assert {contract(c) for c in restricted} == set(ds)
    assert {duplicate(d) for d in ds} == set(restricted)
    for a, b in combinations(ds, 2):
        assert duplicate(join(a, b)) == join(duplicate(a), duplicate(b))
        counts['binary_join_checks'] += 1
    kt = join_value(restricted, p)
    kq = join_value(ds, q)
    assert kt == kq == euler(dq['facets']), (p, q, kt, kq, dq)
    cp, cq, ci = connected(p), connected(q), connected(inflated)
    assert cp == cq == ci
    old, new = euler(dp['facets']), euler(di['facets'])
    if cp and len(set(p)) >= 2:
        assert kt == 0
        assert new == old
        if p[2] == 0:
            assert old == 0
            counts['connected_initial_three_run_zero'] += 1
        counts['connected_multiclass'] += 1
        counts['connected_nonzero'] += int(old != 0)
        if len(cs) == 2 and old == -1:
            assert any(c[0] == c[1] and c.count(c[0]) == 2 for c in cs)
            assert di['generators'] == 3 and new == -1
            counts['two_to_three_survivors'] += 1
    elif kt:
        counts['nonzero_restricted_outside_hypotheses'] += 1
        if len(nonzero_examples) < 5:
            nonzero_examples.append({'pattern': p, 'restricted': kt,
                                     'old': old, 'inflated': new})
    if independent:
        assert set(cs) == set(generators(p)[0])
        assert set(ds) == set(generators(q)[0])
        ics = generators(inflated)[0]
        assert old == join_value(cs, p)
        assert new == join_value(ics, inflated)
        counts['four_endpoint_and_original_join_replays'] += 1
    counts['pattern_tests'] += 1


for profile in [(5,)] + [(5, k) for k in range(1, 9)] + [
        (5, 2, 2), (5, 2, 3), (5, 3, 3), (5, 4, 4), (5, 5, 5)]:
    count = 0
    for p in patterns(profile):
        check(p, independent=len(p) <= 13)
        count += 1
    profiles[','.join(map(str, profile))] = count
    print(profile, count, flush=True)

rng = random.Random(2026103104)
for profile in [(5, 4, 5), (5, 6, 5), (5, 5, 5, 5), (5, 7, 3), (5, 4, 4, 4)]:
    for _ in range(40):
        tail = [0] * 3 + [a for a, k in enumerate(profile[1:], 1) for _ in range(k)]
        rng.shuffle(tail)
        check((0, 0) + tuple(tail), independent=True)
    profiles[','.join(map(str, profile)) + ' seeded probes'] = 40

out = {'status': 'VERIFIED-COMP', 'counts': dict(sorted(counts.items())),
       'profiles': profiles, 'nonzero_restricted_examples': nonzero_examples,
       'scope': 'Exhaustive distinguished initial-pair profiles as listed, plus seeded probes. '
                'No full first-excess or all-length census. Fast compatibility and four-endpoint '
                'replays share local catalogue generation; independence is partial.'}
dest = Path(__file__).with_name('checks.json')
dest.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, sort_keys=True))

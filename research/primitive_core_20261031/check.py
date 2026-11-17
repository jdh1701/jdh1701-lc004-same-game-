"""Exhaustive star search, complete ORIGINAL-family replay, and cross-checks.

No claimed A035617 terms. The structural/counting bridge is a paper proof.
Large witness streams are regenerated, hashed, replayed, then discarded.
"""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, permutations
from pathlib import Path
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/ten_attacks_20261030'))
from core import blocks, catalogue, canonical, crossing, generators, join, join_value
from verify_global_nc_bridge import nc_certificates, raw_connected


def normalize(p):
    names = {}
    return tuple(names.setdefault(a, len(names)) for a in p)


def expand(line):
    xs = list(map(int, line.split()))
    assert len(xs) % 6 == 0
    j = len(xs) // 6
    core, weight = [-1]*(3*j), [2]*(3*j)
    for a in range(j):
        x, y, z, r, u, d = xs[6*a:6*a+6]
        assert x < y < z and {x, y, z} == {r, u, d}
        for k in (x, y, z):
            assert core[k] == -1
            core[k] = a
        weight[r] = 1
    assert all(a >= 0 for a in core)
    return normalize(tuple(a for a, w in zip(core, weight) for _ in range(w)))


def rotations(p):
    return {normalize(p[i:] + p[:i]) for i in range(len(p))}


def independent_small_census(j):
    """Generate NC certificates first, then all pair/triple matchings.

    Every feasible five-pattern occurs, since each class has exactly one pair
    and one triple in every original certificate. No run-shape or SCC filter.
    """
    families = defaultdict(set)
    certs = nc_certificates(j, j)
    incidences = 0
    for bs in certs:
        pairs = [b for b in bs if len(b) == 2]
        triples = [b for b in bs if len(b) == 3]
        c = canonical(bs, 5*j)
        for ts in permutations(triples):
            gs = [tuple(sorted(a+b)) for a, b in zip(pairs, ts)]
            p = canonical(gs, 5*j)
            families[p].add(c)
            incidences += 1
    survivors = set()
    connected = 0
    distribution = Counter()
    for p, fs in families.items():
        if not raw_connected(blocks(p)):
            continue
        connected += 1
        k = join_value(fs, p)
        distribution[k] += 1
        if k:
            assert k == -1 and len(fs) == 2
            survivors.add(p)
    return survivors, {'classes': j, 'nc_certificates': len(certs),
                      'incidences': incidences, 'feasible_patterns': len(families),
                      'connected_patterns': connected,
                      'coefficient_distribution': dict(sorted(distribution.items()))}


def common_gap_check():
    stats = Counter()
    for n in range(4, 11):
        cs = catalogue(n)
        for c, d in combinations(cs, 2):
            stats['certificate_pairs'] += 1
            p = join(c, d)
            gs = blocks(p)
            if len(gs) < 2 or not raw_connected(gs):
                continue
            stats['connected_nontrivial_pairs'] += 1
            for g in gs:
                for u, v in zip(g, g[1:] + g[:1]):
                    if c[u] == c[v] and d[u] == d[v]:
                        stats['shared_cyclic_class_edges'] += 1
                        stats['wraparound_edges'] += int(v < u)
                        assert (u+1) % n == v
    return dict(stats)


def local_catalogue_check():
    cs = catalogue(5)
    stats = Counter()
    for s, t in permutations(cs, 2):
        a = set(next(b for b in blocks(s) if len(b) == 2))
        b = set(next(b for b in blocks(t) if len(b) == 2))
        if a & b:
            stats['overlap_cases'] += 1
            assert any(s[i] == s[(i+1) % 5] and t[i] == t[(i+1) % 5]
                       and i not in a and i not in b for i in range(5))
        else:
            stats['disjoint_cases'] += 1
            assert any(a == {i, (i+1) % 5} and t[i] == t[(i+1) % 5]
                       for i in range(5))
    return dict(stats)


def main():
    results = {'scope': 'connected all-five survivor cores; NOT A035617 terms',
               'local_catalogue': local_catalogue_check(),
               'common_circular_gap': common_gap_check(),
               'search_and_complete_replay': [], 'independent_small_census': []}
    old_counts = {2: 5, 3: 35, 4: 415, 5: 6455}
    with tempfile.TemporaryDirectory(prefix='lc004-star-') as temp:
        temp = Path(temp)
        search, replay = temp / 'search', temp / 'replay'
        for src, exe in [('star_search.cpp', search), ('replay.cpp', replay)]:
            subprocess.run(['g++', '-std=c++17', '-O3', '-Wall', '-Wextra',
                            str(HERE / src), '-o', str(exe)], check=True)
        for j in range(2, 8):
            witness = temp / 'witnesses.txt'
            count = json.loads(subprocess.check_output([str(search), str(j), str(witness)]))
            check = json.loads(subprocess.check_output([str(replay), str(j), str(witness)]))
            assert check['complete_original_family_replays'] == count['strong_star_pairs']
            assert count['orbit_weight_integral']
            assert count['all_five_survivors']*3 == 5*count['strong_star_pairs']
            if j in old_counts:
                assert count['all_five_survivors'] == old_counts[j]
            digest, samples, rows = sha256(), [], 0
            expanded = set()
            with witness.open('rb') as f:
                for line in f:
                    digest.update(line)
                    if rows < 8:
                        samples.append(line.decode().rstrip()+'\n')
                    if j <= 5:
                        expanded.update(rotations(expand(line)))
                    rows += 1
            assert rows == count['strong_star_pairs']
            if j <= 5:
                assert len(expanded) == count['all_five_survivors']
            # A third implementation replays deterministic original-position samples.
            for line in samples:
                p = expand(line)
                fs, _, _ = generators(p)
                assert len(fs) == 2 and join_value(fs, p) == -1
                runs = Counter()
                for i, a in enumerate(p):
                    if p[i-1] != a:
                        k = 1
                        while p[(i+k) % len(p)] == a:
                            k += 1
                        runs[(a, k)] += 1
                assert all(runs[a, 1] == 1 and runs[a, 2] == 2 for a in set(p))
            (HERE / f'sample_{j}.txt').write_text(''.join(samples))
            record = {**count, **check, 'witness_sha256': digest.hexdigest(),
                      'python_original_samples': len(samples),
                      'three_run_first_excess_layer': 2*(5*j+1)*count['all_five_survivors']//5}
            if j <= 5:
                record['explicit_rotation_union'] = len(expanded)
            if j <= 3:
                original, census = independent_small_census(j)
                assert original == expanded
                results['independent_small_census'].append(census)
            results['search_and_complete_replay'].append(record)
            print(json.dumps(record, sort_keys=True), flush=True)
    # A connected proper star pair can still have a THIRD original certificate.
    bad = '0 2 4 0 2 4 1 3 6 3 6 1 5 8 10 8 10 5 7 9 11 11 7 9'
    p = expand(bad)
    fs, _, choices = generators(p)
    assert raw_connected(blocks(p)) and len(fs) == 3 and join_value(fs, p) == 0
    results['rejected_shortcut'] = {'pattern': list(p), 'generators': len(fs),
                                    'choices': choices, 'coefficient': 0}
    (HERE / 'checks.json').write_text(json.dumps(results, indent=2, sort_keys=True)+'\n')
    print('PASS exhaustive search, complete family replay, circular gaps, independent small census')


if __name__ == '__main__':
    main()

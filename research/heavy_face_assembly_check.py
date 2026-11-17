"""Adversarial finite audit of the full structural Face Lemma.

The global oracle filters *all* set partitions, rather than recursing on
noncrossing intervals or assuming face decomposition. It is cross-checked
against maximal-run deletion and the earlier recursive certificate solver.
All calculations use exact finite sets and integers.
"""
from itertools import combinations, product
from pathlib import Path
import json
import time

from rigid_face_geometry_check import patterns, canonical, wins, certificates, faces


def blocks_of(labels):
    return tuple(tuple(i for i, a in enumerate(labels) if a == label)
                 for label in sorted(set(labels)))


def partition_key(blocks):
    return tuple(sorted(tuple(sorted(b)) for b in blocks))


def brute_certificate_shapes(n):
    out = []
    for labels in patterns(n):
        blocks = blocks_of(labels)
        if any(len(b) not in (2, 3) for b in blocks):
            continue
        # Independent direct four-position predicate, including self pairs.
        if any(labels[a] == labels[c] and labels[b] == labels[d]
               for a, b, c, d in combinations(range(n), 4)):
            continue
        out.append(partition_key(blocks))
    return out


def skeleton_noncrossing(w):
    rigid = {a for a in set(w) if w.count(a) in (2, 3)}
    return not any(w[a] == w[c] and w[b] == w[d] and
                   w[a] in rigid and w[b] in rigid
                   for a, b, c, d in combinations(range(len(w)), 4))


def conditions(w):
    _, fs = faces(w)
    return (all(w.count(a) >= 2 for a in set(w)),
            skeleton_noncrossing(w),
            all(wins(canonical(tuple(w[i] for i in f))) for f in fs))


def run(max_n=10):
    rows = []
    minimal_counterexamples = {}
    hypothesis_names = ('no_singleton', 'noncrossing_skeleton', 'winning_faces')
    for n in range(max_n + 1):
        shapes = brute_certificate_shapes(n)
        row = dict(n=n, patterns=0, eligible=0, winning=0,
                   certificate_shapes=len(shapes), global_certificates=0,
                   assembled_certificates=0, exact_product_checks=0)
        for w in patterns(n):
            row['patterns'] += 1
            no_singleton, skel_nc, faces_win = conditions(w)
            direct_win = wins(w)
            assert direct_win == (no_singleton and skel_nc and faces_win), w
            flags = (no_singleton, skel_nc, faces_win)
            if not direct_win:
                for j, name in enumerate(hypothesis_names):
                    if not flags[j] and all(flag for k, flag in enumerate(flags) if k != j):
                        minimal_counterexamples.setdefault(name, w)
            row['winning'] += direct_win
            if not no_singleton:
                continue
            row['eligible'] += 1
            brute = {c for c in shapes
                     if all(all(w[i] == w[b[0]] for i in b) for b in c)}
            recursive = {partition_key(c) for c in certificates(w)}
            assert brute == recursive, ('independent certificate oracle', w)
            assert bool(brute) == direct_win, ('deletion correspondence', w)
            row['global_certificates'] += len(brute)
            if not skel_nc:
                assert not brute
                continue
            rigid, fs = faces(w)
            choices = [certificates(tuple(w[i] for i in f)) for f in fs]
            expected_count = 1
            for local in choices:
                expected_count *= len(local)
            assembled = set()
            for selection in product(*choices):
                c = tuple(rigid) + tuple(tuple(f[i] for i in b)
                    for f, local in zip(fs, selection) for b in local)
                key = partition_key(c)
                assert key not in assembled, ('duplicated assembly', w)
                assert sorted(i for b in c for i in b) == list(range(n))
                assembled.add(key)
            assert assembled == brute, ('gluing image', w)
            assert len(brute) == expected_count, ('product cardinality', w)
            row['assembled_certificates'] += len(assembled)
            row['exact_product_checks'] += 1
        rows.append(row)
        print(json.dumps(row), flush=True)
    # Each of the three hypotheses is individually necessary. Removing it
    # makes the other two accept the following losing word.
    witnesses = {'no_singleton': (0,), 'noncrossing_skeleton': (0, 1, 0, 1),
                 'winning_faces': (0, 1) * 4}
    for removed, w in witnesses.items():
        flags = conditions(w)
        index = list(witnesses).index(removed)
        assert not wins(w) and not flags[index]
        assert all(flag for j, flag in enumerate(flags) if j != index)
    assert set(minimal_counterexamples) == set(hypothesis_names)
    assert len(certificates((0,) * 4)) == 2  # One word, two partitions.
    return dict(scope=f'exhaustive patterns, assembly, and product identity through n={max_n}',
                rows=rows, necessary_hypothesis_counterexamples=witnesses,
                smallest_hypothesis_counterexamples=minimal_counterexamples,
                minimality_scope='first restricted-growth word in increasing length; all shorter words checked',
                interpretation='Counts are certificate partitions, not distinct winning color patterns.')


if __name__ == '__main__':
    start = time.perf_counter()
    result = run()
    result['elapsed_seconds'] = time.perf_counter() - start
    Path('research/heavy_face_assembly_results.json').write_text(
        json.dumps(result, indent=2) + '\n')

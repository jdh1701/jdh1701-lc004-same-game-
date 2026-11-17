"""Independent finite checks for the geometric certificate-face theorem.

No floating point, imported counting formula, or assumed face factorization.
One solver deletes maximal runs. The other recursively constructs all
noncrossing pair/triple certificates. A third face test uses arc separation.
"""
from functools import lru_cache
from itertools import combinations, product
import json
import time


def canonical(word):
    labels = {}
    return tuple(labels.setdefault(x, len(labels)) for x in word)


def patterns(n):
    def rec(w, k):
        if len(w) == n:
            yield w
        else:
            for a in range(k + 1):
                yield from rec(w + (a,), max(k, a + 1))
    yield from rec((), 0)


@lru_cache(None)
def wins(w):
    if not w:
        return True
    i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        if j - i >= 2 and wins(canonical(w[:i] + w[j:])):
            return True
        i = j
    return False


def certificates(w):
    @lru_cache(None)
    def rec(points):
        if not points:
            return ((),)
        a = points[0]
        out = []
        eligible = [i for i in range(1, len(points)) if w[points[i]] == w[a]]
        for size in (2, 3):
            for cuts in combinations(eligible, size - 1):
                ends = (0,) + cuts + (len(points),)
                children = [rec(points[ends[j] + 1:ends[j + 1]]) for j in range(size)]
                for parts in product(*children):
                    out.append(((a,) + tuple(points[c] for c in cuts),) +
                               tuple(b for part in parts for b in part))
        return tuple(out)
    return rec(tuple(range(len(w))))


def crosses(a, b):
    return any(i < j < k < l or j < i < l < k
               for i, k in combinations(sorted(a), 2)
               for j, l in combinations(sorted(b), 2))


def faces(w):
    classes = [tuple(i for i, x in enumerate(w) if x == a) for a in sorted(set(w))]
    rigid = [b for b in classes if len(b) in (2, 3)]
    heavy = [i for b in classes if len(b) >= 4 for i in b]
    chords = [uv for b in rigid for uv in combinations(b, 2)]
    by_signature = {}
    for i in sorted(heavy):
        sig = tuple(u < i < v for u, v in chords)
        by_signature.setdefault(sig, []).append(i)
    return rigid, list(by_signature.values())


def components(blocks, carrier):
    """BFS connectivity, independent of the union-find implementation below."""
    adj = {x: set() for x in carrier}
    for b in blocks:
        local = set(b) & set(carrier)
        for x in local:
            adj[x].update(local)
    comp = {}
    for x in carrier:
        if x in comp:
            continue
        stack = [x]
        comp[x] = x
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in comp:
                    comp[v] = x
                    stack.append(v)
    return comp


def joined(blocks, n):
    parent = list(range(n))
    def root(a):
        while parent[a] != a:
            a = parent[a]
        return a
    for b in blocks:
        for x in b:
            parent[root(x)] = root(b[0])
    return [root(x) for x in range(n)]


def run(max_n=10):
    rows = []
    for n in range(max_n + 1):
        counts = dict(n=n, patterns=0, eligible=0, winning=0, certificates=0,
                      heavy_blocks=0, join_face_checks=0, glued_certificates=0)
        for w in patterns(n):
            counts['patterns'] += 1
            if any(w.count(a) == 1 for a in set(w)):
                assert not wins(w)
                continue
            counts['eligible'] += 1
            rigid, fs = faces(w)
            heavy = [i for f in fs for i in f]
            face_of = {i: k for k, f in enumerate(fs) for i in f}
            for a, b in combinations(heavy, 2):
                lo, hi = sorted((a, b))
                arc_same = not any(any(lo < u < hi for u in c) and
                                   any(u < lo or hi < u for u in c) for c in rigid)
                assert (face_of[a] == face_of[b]) == arc_same
            certs = certificates(w)
            counts['certificates'] += len(certs)
            direct = wins(w)
            predicted = (not any(crosses(a, b) for a, b in combinations(rigid, 2)) and
                         all(wins(canonical(tuple(w[i] for i in f))) for f in fs))
            assert direct == bool(certs) == predicted, (w, direct, bool(certs), predicted)
            counts['winning'] += direct
            for c in certs:
                assert all(set(r) in [set(b) for b in c] for r in rigid)
                for b in c:
                    if b[0] in face_of:
                        counts['heavy_blocks'] += 1
                        assert len({face_of[i] for i in b}) == 1
            if n <= 8:
                for c, d in combinations(certs, 2):
                    global_join = joined(c + d, n)
                    for f in fs:
                        local = components(c + d, f)
                        assert all((global_join[i] == global_join[j]) == (local[i] == local[j])
                                   for i, j in combinations(f, 2))
                        counts['join_face_checks'] += 1
                if predicted:
                    local_certs = [certificates(tuple(w[i] for i in f)) for f in fs]
                    assembled = set()
                    for choices in product(*local_certs):
                        blocks = tuple(rigid) + tuple(tuple(f[i] for i in b)
                            for f, c in zip(fs, choices) for b in c)
                        key = tuple(sorted(tuple(sorted(b)) for b in blocks))
                        assert key not in assembled
                        assembled.add(key)
                    expected = {tuple(sorted(tuple(sorted(b)) for b in c)) for c in certs}
                    assert assembled == expected
                    counts['glued_certificates'] += len(assembled)
        rows.append(counts)
        print(json.dumps(counts), flush=True)
    # A heavy COLOR class can span faces; its certificate BLOCKS cannot.
    w = (0, 0, 1, 0, 0, 1)
    rigid, fs = faces(w)
    assert wins(w) and fs == [[0, 1], [3, 4]]
    # Full carrier is necessary: actual certificates fail on a partial face.
    c, d, f = ((0, 1), (2, 3)), ((0, 3), (1, 2)), [0, 2]
    assert c in certificates((0,) * 4) and d in certificates((0,) * 4)
    assert joined(c + d, 4)[0] == joined(c + d, 4)[2]
    assert components(c + d, f)[0] != components(c + d, f)[2]
    return {'rows': rows, 'counterexamples': {
        'heavy_color_spans_faces': {'word': w, 'rigid': rigid, 'faces': fs},
        'partial_face_join_failure': {'certificates': [c, d], 'carrier': f}},
        'scope': 'exhaustive patterns through n=10; certificate pair joins and gluing through n=8'}


if __name__ == '__main__':
    start = time.perf_counter()
    result = run()
    result['elapsed_seconds'] = time.perf_counter() - start
    from pathlib import Path
    Path('research/rigid_face_geometry_results.json').write_text(json.dumps(result, indent=2) + '\n')

"""Exact falsification of multiplicity-only safe-deletion proposals.

Independent breadth-first search retains original labels and maximal-run
moves. It is checked against the existing memoized recursive solver.
No novelty or universal positive greedy rule is claimed.
"""
from collections import Counter, deque
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import json
from rigid_face_geometry_check import wins, certificates


def heavy_patterns(n):
    def rec(word, counts):
        remain = n - len(word)
        deficit = sum(max(0, 4-c) for c in counts)
        if deficit > remain:
            return
        if not remain:
            yield word
            return
        for a in range(len(counts)):
            updated = counts.copy()
            updated[a] += 1
            yield from rec(word + (a,), updated)
        if remain >= 4 + deficit:
            yield from rec(word + (len(counts),), counts + [1])
    yield from rec((), [])


@lru_cache(None)
def heavy_pattern_count(n):
    # Count by the block containing the least position: independent of generator.
    if n == 0:
        return 1
    return sum(comb(n-1, k-1)*heavy_pattern_count(n-k) for k in range(4, n+1))


def moves(word):
    i = 0
    while i < len(word):
        j = i + 1
        while j < len(word) and word[j] == word[i]:
            j += 1
        if j-i >= 2:
            yield i, j, word[:i] + word[j:]
        i = j


def bfs(word):
    seen = {word: []}
    queue = deque([word])
    while queue:
        state = queue.popleft()
        if not state:
            return True, seen[state]
        for i, j, child in moves(state):
            if child not in seen:
                seen[child] = seen[state] + [[i, j]]
                queue.append(child)
    return False, [list(w) for w in sorted(seen, key=lambda w: (len(w), w))]


def run(max_n=12):
    first = {}
    rows = []
    for n in range(max_n + 1):
        count = winning = 0
        for word in heavy_patterns(n):
            count += 1
            direct, trace = bfs(word)
            assert direct == wins(word), ('independent BFS', word)
            winning += direct
            if not direct:
                continue
            for i, j, child in moves(word):
                loses = not bfs(child)[0]
                for key, threshold in [('no_singleton_safe', 2), ('heavy_preserving_safe', 4)]:
                    if loses and all(c >= threshold for c in Counter(child).values()):
                        if key not in first:
                            assert certificates(word) and not certificates(child)
                            first[key] = dict(word=word, deleted_interval=[i,j], child=child,
                                              winning_path=trace, losing_reachable_states=bfs(child)[1])
        assert count == heavy_pattern_count(n), ('generator completeness', n)
        rows.append(dict(n=n, heavy_patterns=count, winning=winning))
    assert len(first['no_singleton_safe']['word']) == 9
    assert len(first['heavy_preserving_safe']['word']) == 10
    family_checks = 0
    for r,s,t in product(range(2,9),range(2,6),range(2,9)):
        word = (0,)*r + (1,) + (0,)*s + (1,)*t + (0,1)
        child = (0,)*r + (1,)*(t+1) + (0,1)
        assert (r+1,r+1+s,child) in [(i,j,u) for i,j,u in moves(word)]
        assert bfs(word)[0] and not bfs(child)[0]
        assert Counter(child)[0] == r+1 and Counter(child)[1] == t+2
        family_checks += 1
    return dict(scope='all color patterns with each class size at least four, n<=12',
                rows=rows, minimal_counterexamples=first, family_checks=family_checks,
                family='A^r B A^s B^t A B, r,s,t >= 2; delete A^s',
                formal_boundary='Concrete compressed run-state obstruction certified separately in Lean; family and minimality are not Lean-certified',
                novelty='Not assessed; this is a discriminating failure result for proposed counting strategies')


if __name__ == '__main__':
    result = run()
    Path('research/heavy_greedy_obstruction_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

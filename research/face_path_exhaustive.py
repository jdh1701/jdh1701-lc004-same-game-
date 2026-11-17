"""Exhaustive finite check: join then restrict versus restrict then join."""
from itertools import combinations

def partitions(n):
    def rec(i, blocks):
        if i == n:
            yield tuple(tuple(b) for b in blocks)
            return
        for k in range(len(blocks)):
            blocks[k].append(i)
            yield from rec(i + 1, blocks)
            blocks[k].pop()
        blocks.append([i])
        yield from rec(i + 1, blocks)
        blocks.pop()
    yield from rec(0, [])

def relation(part, n):
    r = list(range(n))
    for block in part:
        for i in block:
            r[i] = block[0]
    return r

def join(p, q, n):
    parent = list(range(n))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for r in (p, q):
        for i in range(n):
            parent[root(i)] = root(r[i])
    return [root(i) for i in range(n)]

def check(n):
    patterns = [relation(part, n) for part in partitions(n)]
    total = failures = 0
    witness = None
    for p in patterns:
        for q in patterns:
            joined = join(p, q, n)
            for k in range(n + 1):
                for face in combinations(range(n), k):
                    total += 1
                    edges = {i: set() for i in face}
                    for i in face:
                        for j in face:
                            if p[i] == p[j] or q[i] == q[j]:
                                edges[i].add(j)
                    components = {}
                    seen = set()
                    for i in face:
                        if i in seen:
                            continue
                        stack = [i]
                        seen.add(i)
                        while stack:
                            u = stack.pop()
                            components[u] = i
                            for v in edges[u] - seen:
                                seen.add(v)
                                stack.append(v)
                    pairs = list(combinations(face, 2))
                    local = tuple(components[i] == components[j] for i, j in pairs)
                    global_restricted = tuple(joined[i] == joined[j] for i, j in pairs)
                    assert all(not a or b for a, b in zip(local, global_restricted))
                    if local != global_restricted:
                        failures += 1
                        if witness is None:
                            witness = (p, q, face)
    return dict(n=n, cases=total, failures=failures, witness=witness)

if __name__ == "__main__":
    expected = [(1, 0), (2, 0), (16, 0), (200, 6)]
    for n, (cases, failures) in enumerate(expected):
        result = check(n)
        assert (result["cases"], result["failures"]) == (cases, failures), result
        print(result)

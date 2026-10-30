"""Independent finite validation of the internal-path criterion for join restriction."""
from itertools import combinations
from face_path_exhaustive import partitions, relation, join

def connected(vertices, edge):
    seen = set()
    comps = {}
    for start in vertices:
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        while stack:
            u = stack.pop()
            comps[u] = start
            for v in vertices:
                if v not in seen and edge(u, v):
                    seen.add(v)
                    stack.append(v)
    return comps

def test(n):
    ps = [relation(part, n) for part in partitions(n)]
    cases = failures = 0
    for p in ps:
        for q in ps:
            full = join(p, q, n)
            for k in range(n+1):
                for face in combinations(range(n), k):
                    local = connected(face, lambda i,j: p[i]==p[j] or q[i]==q[j])
                    for i,j in combinations(face,2):
                        cases += 1
                        global_connected = full[i] == full[j]
                        local_connected = local[i] == local[j]
                        # Every internal path is global; path locality is exactly
                        # the missing converse on each pair.
                        assert not local_connected or global_connected
                        if global_connected != local_connected:
                            failures += 1
    return cases, failures

if __name__ == "__main__":
    for n in range(5):
        cases, failures = test(n)
        print(f"n={n} selected-pairs={cases} external-bridge-pairs={failures}")
    assert test(3)[1] == 6

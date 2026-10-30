"""Independent, from-scratch check of GPT's SCC survivor-recognition theorem
(ChoiceImplicationRecognition.lean, commit c365c2a):

  Let A be the exact solution set of a complete symmetric binary-constraint
  network C on finite domains D_1..D_k, majority-closed, with one covering
  pivot edge (ChoiceSmallEdge): exists i,j,p,q such that every solution has
  x_i=p or x_j=q. Let a,b in A differ at every coordinate. Build directed
  graph G: edge i->j iff i!=j and NOT C(i,j,b_i,a_j). Claim: A = {a,b} iff
  G is strongly connected.

This script builds random small CSP instances satisfying the hypotheses by
construction (majority-closed relation shapes: universal / rectangle /
two-fan / bijection-matching, as classified earlier this project), brute
forces the full solution set A, finds any fully-differing pair a,b in A,
builds the SCC graph from the RAW relations C (never from A), and checks
the biconditional against the ground-truth brute-force fact "A has exactly
two elements, namely a and b".
"""
import itertools
import random

random.seed(20261029)


def majority(x, y, z):
    return y if y == z else x


def is_majority_closed(dom_i, dom_j, C):
    for x1 in dom_i:
        for y1 in dom_j:
            if not C(x1, y1):
                continue
            for x2 in dom_i:
                for y2 in dom_j:
                    if not C(x2, y2):
                        continue
                    for x3 in dom_i:
                        for y3 in dom_j:
                            if not C(x3, y3):
                                continue
                            mx = majority(x1, x2, x3)
                            my = majority(y1, y2, y3)
                            if not C(mx, my):
                                return False
    return True


def random_closed_relation(dom_i, dom_j, rng):
    """Build a relation of one of the known majority-closed shapes."""
    shape = rng.choice(["universal", "rectangle", "fan", "bijection", "empty"])
    if shape == "universal":
        return lambda x, y: True, shape
    if shape == "empty":
        return lambda x, y: False, shape
    if shape == "rectangle":
        U = set(rng.sample(dom_i, rng.randint(1, len(dom_i))))
        V = set(rng.sample(dom_j, rng.randint(1, len(dom_j))))
        return (lambda x, y, U=U, V=V: (x in U) and (y in V)), shape
    if shape == "fan":
        a = rng.choice(dom_i)
        b = rng.choice(dom_j)
        return (lambda x, y, a=a, b=b: (x == a) or (y == b)), shape
    if shape == "bijection":
        n = min(len(dom_i), len(dom_j))
        xs = rng.sample(dom_i, n)
        ys = rng.sample(dom_j, n)
        pairs = set(zip(xs, ys))
        return (lambda x, y, pairs=pairs: (x, y) in pairs), shape
    raise AssertionError


def build_instance(rng, k, dom_size):
    doms = [list(range(dom_size)) for _ in range(k)]
    C = {}
    shapes = {}
    for i in range(k):
        for j in range(k):
            if i == j:
                continue
            if (j, i) in C:
                f = C[(j, i)]
                C[(i, j)] = lambda x, y, f=f: f(y, x)
                shapes[(i, j)] = shapes[(j, i)]
                continue
            rel, shape = random_closed_relation(doms[i], doms[j], rng)
            C[(i, j)] = rel
            shapes[(i, j)] = shape
    return doms, C, shapes


def solutions(doms, C, k):
    out = []
    for tup in itertools.product(*doms):
        ok = True
        for i in range(k):
            for j in range(k):
                if i == j:
                    continue
                if not C[(i, j)](tup[i], tup[j]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(tup)
    return out


def has_small_edge(doms, A, k):
    for i in range(k):
        for j in range(k):
            if i == j:
                continue
            for p in doms[i]:
                for q in doms[j]:
                    if all(a[i] == p or a[j] == q for a in A):
                        return (i, j, p, q)
    return None


def strongly_connected(k, edges):
    def reach(src):
        seen = {src}
        stack = [src]
        while stack:
            u = stack.pop()
            for (uu, v) in edges:
                if uu == u and v not in seen:
                    seen.add(v)
                    stack.append(v)
        return seen
    for i in range(k):
        if len(reach(i)) != k:
            return False
    return True


def run_trial(rng, k, dom_size):
    doms, C, shapes = build_instance(rng, k, dom_size)
    # verify majority closure of every pairwise relation independently
    for i in range(k):
        for j in range(k):
            if i == j:
                continue
            if not is_majority_closed(doms[i], doms[j], C[(i, j)]):
                return None  # shouldn't happen by construction; guard anyway
    A = solutions(doms, C, k)
    if len(A) < 2:
        return None
    edge0 = has_small_edge(doms, A, k)
    if edge0 is None:
        return None
    # find a fully-differing pair in A
    pair = None
    for a, b in itertools.combinations(A, 2):
        if all(a[t] != b[t] for t in range(k)):
            pair = (a, b)
            break
    if pair is None:
        return None
    a, b = pair
    edges = set()
    for i in range(k):
        for j in range(k):
            if i == j:
                continue
            if not C[(i, j)](b[i], a[j]):
                edges.add((i, j))
    scc = strongly_connected(k, edges)
    ground_truth_rigid = (len(A) == 2 and set(A) == {a, b})
    return (ground_truth_rigid, scc, len(A), shapes)


def main():
    rng = random.Random(20261029)
    total = 0
    mismatches = []
    checked_rigid = 0
    checked_nonrigid = 0
    for trial in range(4000):
        k = rng.randint(2, 5)
        dom_size = rng.randint(2, 4)
        res = run_trial(random.Random(rng.random()), k, dom_size)
        if res is None:
            continue
        ground_truth_rigid, scc, size_A, shapes = res
        total += 1
        if ground_truth_rigid:
            checked_rigid += 1
        else:
            checked_nonrigid += 1
        if ground_truth_rigid != scc:
            mismatches.append((k, dom_size, size_A, ground_truth_rigid, scc, shapes))
    print(f"total checked: {total}, rigid: {checked_rigid}, "
          f"nonrigid: {checked_nonrigid}, mismatches: {len(mismatches)}")
    for m in mismatches[:10]:
        print("MISMATCH:", m)


if __name__ == "__main__":
    main()

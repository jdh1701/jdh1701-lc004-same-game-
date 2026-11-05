"""
Independent stress test of GPT's GENERALIZED abstract theorem
(LC004/ChoiceAbstractCancellation.lean, choiceAlternatingSum_zero_of_local_constraints):
only ONE coordinate-pair needs to be a "small edge" (covered by one row + one
column); OTHER nonuniversal edges may be arbitrary majority-closed relations,
including FULL-SIZE bijections (not restricted to size <=2). Only requirement:
overall cut-connectivity (every nontrivial subset is crossed by some nonuniversal
edge) and >=3 solutions. This is strictly more general than what was stress-
tested earlier in this session (verify_abstract_theorem3.py required every
nonuniversal edge to be two-fan/matching-2).

Written fresh, independent of GPT's and Claude's prior scripts.
"""
import itertools, random

def solve_csp(domains, edges):
    sols = []
    for assignment in itertools.product(*domains):
        ok = True
        for (i, j), allowed in edges.items():
            if (assignment[i], assignment[j]) not in allowed:
                ok = False
                break
        if ok:
            sols.append(assignment)
    return sols

def projection_c(A, k):
    total = 0
    for mask in range(1 << k):
        T = [i for i in range(k) if (mask >> i) & 1]
        proj_set = set(tuple(a[i] for i in T) for a in A)
        sign = 1 if (len(T) % 2 == 0) else -1
        total += sign * len(proj_set)
    return total

def make_two_fan(dom_i, dom_j, rng):
    s = rng.choice(dom_i); t = rng.choice(dom_j)
    return {(x, y) for x in dom_i for y in dom_j if x == s or y == t}

def make_full_bijection(dom_i, dom_j, rng):
    # a random permutation-style full-size bijection between equal-size domains
    perm = dom_j[:]
    rng.shuffle(perm)
    return {(dom_i[k], perm[k]) for k in range(len(dom_i))}

def make_universal(dom_i, dom_j):
    return {(x, y) for x in dom_i for y in dom_j}

def has_small_edge_on_tree(edges, tree_edges, rng, domains):
    # force exactly one tree edge to be a two-fan (guarantees hedge)
    forced = rng.choice(tree_edges)
    return forced

def random_general_csp(k, domain_size, rng):
    domains = [list(range(domain_size)) for _ in range(k)]
    nodes = list(range(k)); rng.shuffle(nodes)
    tree_edges = [(min(nodes[i], nodes[i+1]), max(nodes[i], nodes[i+1])) for i in range(k-1)]
    forced_small = rng.choice(tree_edges)
    edges = {}
    for e in tree_edges:
        i, j = e
        if e == forced_small:
            edges[e] = make_two_fan(domains[i], domains[j], rng)
        else:
            kind = rng.choice(['fan', 'bij', 'universal'])
            if kind == 'fan':
                edges[e] = make_two_fan(domains[i], domains[j], rng)
            elif kind == 'bij':
                edges[e] = make_full_bijection(domains[i], domains[j], rng)
            else:
                edges[e] = make_universal(domains[i], domains[j])
    return domains, edges, forced_small

def main():
    rng = random.Random(24681357)
    trials = 0; nontrivial = 0; failures = []
    max_A = 0
    for k in range(2, 8):
        for domain_size in range(2, 6):
            for _ in range(150):
                trials += 1
                domains, edges, forced = random_general_csp(k, domain_size, rng)
                A = solve_csp(domains, edges)
                if len(A) < 3:
                    continue
                # confirm support: every domain value occurs (else skip -- not matching
                # the theorem's hsupport+Nontrivial hypothesis cleanly)
                full_support = all(
                    all(any(a[v] == val for a in A) for val in range(domain_size))
                    for v in range(k)
                )
                if not full_support:
                    continue
                max_A = max(max_A, len(A))
                c = projection_c(A, k)
                nontrivial += 1
                if c != 0:
                    failures.append((k, domain_size, len(A), c, forced))
        print(f"  k={k} done, trials={trials} nontrivial={nontrivial} failures={len(failures)}", flush=True)

    print(f"FINAL trials={trials} nontrivial={nontrivial} failures={len(failures)} max|A|={max_A}")
    for f in failures[:10]:
        print("FAILURE:", f)

if __name__ == "__main__":
    main()

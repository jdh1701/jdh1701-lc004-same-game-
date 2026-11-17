import itertools, random, sys, time

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

def make_matching2(dom_i, dom_j, rng):
    xs = rng.sample(dom_i, 2); ys = rng.sample(dom_j, 2); rng.shuffle(ys)
    return {(xs[0], ys[0]), (xs[1], ys[1])}

def random_csp(k, domain_size, rng, extra_edge_prob=0.4):
    domains = [list(range(domain_size)) for _ in range(k)]
    nodes = list(range(k)); rng.shuffle(nodes)
    tree_edges = [(min(nodes[i], nodes[i+1]), max(nodes[i], nodes[i+1])) for i in range(k-1)]
    edges = {}
    for (i, j) in tree_edges:
        kind = rng.choice(['fan', 'match'])
        edges[(i, j)] = make_two_fan(domains[i], domains[j], rng) if kind == 'fan' else make_matching2(domains[i], domains[j], rng)
    for i in range(k):
        for j in range(i+1, k):
            if (i, j) in edges: continue
            if rng.random() < extra_edge_prob:
                kind = rng.choice(['fan', 'match'])
                edges[(i, j)] = make_two_fan(domains[i], domains[j], rng) if kind == 'fan' else make_matching2(domains[i], domains[j], rng)
    return domains, edges

def main():
    rng = random.Random(135792468)
    trials = 0; nontrivial = 0; two_cases = 0; two_fail = 0
    failures = []; max_A_seen = 0
    t0 = time.time()
    combos = [(k, d) for k in range(2, 9) for d in range(2, 6) if d**k <= 60000]
    for k, domain_size in combos:
        for _ in range(100):
            trials += 1
            domains, edges = random_csp(k, domain_size, rng)
            A = solve_csp(domains, edges)
            if len(A) < 2: continue
            const_coord = any(len(set(a[c] for a in A)) == 1 for c in range(k))
            if const_coord: continue
            max_A_seen = max(max_A_seen, len(A))
            c = projection_c(A, k)
            if len(A) == 2:
                two_cases += 1
                if c != -1:
                    two_fail += 1; failures.append((k, domain_size, len(A), c))
            else:
                nontrivial += 1
                if c != 0:
                    failures.append((k, domain_size, len(A), c, A))
        print(f"  done k={k} d={domain_size} trials_so_far={trials} nontrivial={nontrivial} failures={len(failures)} t={time.time()-t0:.1f}s", flush=True)

    print(f"FINAL trials={trials} two_cases={two_cases} two_fail={two_fail} nontrivial={nontrivial} failures={len(failures)} max|A|={max_A_seen}")
    for f in failures[:10]:
        print("FAILURE:", f)

if __name__ == "__main__":
    main()

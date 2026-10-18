#!/usr/bin/env python3
"""Discriminate coefficient factorization from a false free-additivity model.

All transforms are formal polynomial identities; no probability measure is
asserted. Testing component factorization does not independently predict the
connected weights themselves. The small-length pattern was seen before this
script: the subsequent ranges are extension checks, not preregistered trials.
"""
from collections import Counter
from itertools import combinations
from math import prod
from pathlib import Path
import csv
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from partition_count import canonical, witnesses, signed_constraints
from experiments import restricted_growth


def nc_components(p):
    """Iteratively merge interleaving blocks until noncrossing."""
    closed = p
    while True:
        conflict = next(((closed[a], closed[b])
                         for a,b,c,d in combinations(range(len(p)),4)
                         if closed[a] == closed[c] and closed[b] == closed[d]
                         and closed[a] != closed[b]), None)
        if conflict is None:
            return [tuple(i for i,x in enumerate(closed) if x == label)
                    for label in sorted(set(closed))]
        a,b = conflict
        closed = canonical(tuple(a if x == b else x for x in closed))


def add(p, r, scale=1):
    out = Counter(p)
    for k,a in r.items():
        out[k] += scale*a
    return {k:a for k,a in out.items() if a}


def mul(p, r):
    out = Counter()
    for i,a in p.items():
        for j,b in r.items():
            out[i+j] += a*b
    return {k:a for k,a in out.items() if a}


def series_mul(a, b, cap):
    out = [{} for _ in range(cap+1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b[:cap-i+1]):
            out[i+j] = add(out[i+j], mul(x,y))
    return out


def orbit_moments(nmax):
    moments = [{} for _ in range(nmax+1)]
    source = HERE.parents[1] / 'checkpoint_2026_10_17/data/orbit_polynomials.csv'
    for row in csv.DictReader(source.open()):
        n,k = int(row['n']),int(row['k'])
        if n > nmax:
            continue
        term = {0:1}
        for i in range(k):
            term = mul(term,{1:1,0:-i})
        moments[n] = add(moments[n], term, int(row['solvable_orbits']))
    return moments


def formal_cumulants(moments):
    """M(z)=1+sum_k R_k(q)*(z*M(z))^k; triangular coefficient extraction."""
    nmax = len(moments)-1
    powers = [[{0:1}]+[{} for _ in range(nmax)]]
    for k in range(1,nmax+1):
        powers.append(series_mul(powers[-1],moments,nmax))
    cumulants = [{} for _ in range(nmax+1)]
    for n in range(1,nmax+1):
        value = moments[n]
        for k in range(1,n):
            value = add(value,mul(cumulants[k],powers[k][n-k]),-1)
        cumulants[n] = value
    return cumulants


def main():
    nmax = 12
    started = time.monotonic()
    maps, connected, rows = {0:{():1},1:{}}, [{}], []
    nontrivial_checks = zero_checks = 0
    block_only_counterexample = None
    for n in range(1,nmax+1):
        if n >= 2:
            maps[n],_ = signed_constraints(witnesses(n))
        coeff = maps[n]
        conn = Counter()
        for p,a in coeff.items():
            if len(nc_components(p)) == 1:
                conn[len(set(p))] += a
        connected.append(dict(conn))
        # All equality types through 10; larger lengths: all nonzero support.
        domain = restricted_growth(n) if n <= 10 else iter(coeff)
        tested = 0
        for p in domain:
            actual = coeff.get(p,0)
            sizes = Counter(p)
            if 1 in sizes.values():
                assert actual == 0
                zero_checks += 1
                continue
            components = nc_components(p)
            if len(components) > 1:
                predicted = prod(maps[len(ix)].get(canonical(tuple(p[i] for i in ix)),0)
                                 for ix in components)
                assert actual == predicted, ('component factorization',p,actual,predicted)
                tested += 1
                nontrivial_checks += 1
                zero_checks += actual == 0
            if block_only_counterexample is None:
                predicted = prod(maps[k].get((0,)*k,0) for k in sizes.values())
                if actual != predicted:
                    block_only_counterexample = dict(n=n,partition=p,actual=actual,
                                                     block_size_product=predicted)
        row = dict(n=n, signed_terms=len(coeff), connected_polynomial=dict(conn),
                   nontrivial_factorization_checks=tested)
        rows.append(row)
        print(json.dumps(row),flush=True)
    moments = orbit_moments(nmax)
    transformed = formal_cumulants(moments)
    assert transformed == connected, ('independent orbit transform',transformed,connected)
    failures = [dict(n=n,actual=connected[n],
                     linear_prediction={1:sum(connected[n].values())})
                for n in range(1,nmax+1)
                if connected[n] != ({1:sum(connected[n].values())}
                                    if sum(connected[n].values()) else {})]
    assert failures[0]['n'] == 10
    assert connected[10] == {1:-161,2:-5}
    result = dict(rows=rows,all_partition_range=[1,10],support_only_range=[11,12],
                  nontrivial_factorization_checks=nontrivial_checks,
                  zero_coefficient_checks=zero_checks,
                  block_size_only_counterexample=block_only_counterexample,
                  free_additivity_counterexamples=failures,
                  orbit_transform_checks=nmax,unexpected_failures=0,
                  elapsed_seconds=time.monotonic()-started)
    (HERE/'data/connected_weights.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}),flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent exact checks. No third-party packages; no probabilistic sampling."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb, prod
from pathlib import Path
import csv
import json
import time

ROOT = Path(__file__).resolve().parent


def canonical(w):
    labels = {}
    return tuple(labels.setdefault(c, len(labels)) for c in w)


def encode(w):
    out = []
    for c in w:
        if out and out[-1][0] == c:
            out[-1] = (c, True)
        else:
            out.append((c, False))
    return tuple(out)


def raw_moves(w):
    i = run = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        if j - i >= 2:
            yield run, w[:i] + w[j:]
        i, run = j, run + 1


@lru_cache(None)
def raw_paths(w):
    if not w:
        return 1
    return sum(raw_paths(v) for _, v in raw_moves(w))


def run_moves(s):
    for i, (_, heavy) in enumerate(s):
        if heavy:
            if 0 < i < len(s) - 1 and s[i-1][0] == s[i+1][0]:
                yield i, s[:i-1] + ((s[i-1][0], True),) + s[i+2:]
            else:
                yield i, s[:i] + s[i+1:]


@lru_cache(None)
def run_paths(s):
    if not s:
        return 1
    return sum(run_paths(t) for _, t in run_moves(s))


@lru_cache(None)
def grammar_solvable(w):
    """Biedl et al., Theorem 2: S -> eps | SS | cSc | cScSc.

    Skip empty SS factors to make recursion strictly length decreasing.
    This recognizer does not use run deletion or the Boolean abstraction.
    """
    n = len(w)
    if n == 0:
        return True
    if n < 2:
        return False
    if any(grammar_solvable(w[:i]) and grammar_solvable(w[i:])
           for i in range(1, n)):
        return True
    if w[0] != w[-1]:
        return False
    if grammar_solvable(w[1:-1]):
        return True
    return any(w[i] == w[0] and grammar_solvable(w[1:i])
               and grammar_solvable(w[i+1:-1]) for i in range(1, n-1))


def firsts(s):
    return [i for i, t in run_moves(s) if run_paths(t)]


def all_paths(s):
    if not s:
        return [()]
    return [(i,) + p for i, t in run_moves(s) for p in all_paths(t)]


def weak_shell_test(s):
    n = len(s)
    return bool(n % 2 and s[n//2][1] and all(
        s[i][0] == s[-1-i][0] and not (s[i][1] and s[-1-i][1])
        for i in range(n//2)))


def restricted_growth(n, max_colors=None, normalized=False):
    def visit(w, k):
        if len(w) == n:
            yield w
            return
        for c in range(k + (max_colors is None or k < max_colors)):
            if normalized and w and c == w[-1]:
                continue
            yield from visit(w + (c,), max(k, c + 1))
    yield from visit((), 0)


def coeff_weight(n, lights, heavies):
    # z^lights * (z^2/(1-z))^heavies.
    extra = n - lights - 2*heavies
    if extra < 0:
        return 0
    if heavies == 0:
        return int(extra == 0)
    return comb(extra + heavies - 1, heavies - 1)


def distinct_shell_coefficient(q, n):
    # H(z) * sum_m (q)_(m+1) * (z^2 + 2*z*H(z))^m.
    total = 0
    for m in range(min(q-1, (n-2)//2) + 1):
        orbit = prod(q-i for i in range(m+1))
        for h in range(m+1):
            total += orbit * comb(m,h) * 2**h * coeff_weight(n,2*m-h,h+1)
    return total


def run():
    start = time.monotonic()
    rows = []
    first_hist = Counter()
    observed_witness = None
    grammar_checks = 0
    reported = Counter()
    for q, nmax in ((2,14),(3,10),(4,8)):
        for n in range(nmax+1):
            solved = unique = distinct = maxpaths = 0
            for w in product(range(q), repeat=n):
                s = encode(w)
                rp, sp = raw_paths(w), run_paths(s)
                assert rp == sp, ('abstraction_paths', w, s, rp, sp)
                assert [(i,encode(v)) for i,v in raw_moves(w)] == list(run_moves(s))
                good = firsts(s)
                assert not w or ((len(good)==1) == (rp==1)), ('uniqueness',w)
                if rp == 1 and w:
                    assert len(s)%2 and good == [len(s)//2], ('median',w)
                    assert tuple(c for c,_ in s) == tuple(c for c,_ in reversed(s))
                    assert weak_shell_test(s), ('necessary_shells',w)
                if n <= 8 and q <= 3:
                    assert grammar_solvable(w) == (rp>0), ('grammar',w)
                    grammar_checks += 1
                is_distinct = bool(s and len(s)%2 and
                    len(set(c for c,_ in s[:len(s)//2+1])) == len(s)//2+1 and
                    tuple(c for c,_ in s) == tuple(c for c,_ in reversed(s)))
                if is_distinct:
                    assert (rp==1) == weak_shell_test(s), ('distinct_shell',w,s,rp)
                    distinct += rp==1
                if observed_witness is None and weak_shell_test(s) and rp!=1:
                    observed_witness = {'word':w, 'runs':s, 'paths':all_paths(s)}
                solved += rp>0
                unique += rp==1
                maxpaths = max(maxpaths,rp)
                first_hist[q,n,len(good)] += 1
                if q<=3 and 1<=n<=8:
                    reported['total'] += 1
                    reported['solvable'] += rp>0
            assert n==0 or distinct == distinct_shell_coefficient(q,n), (q,n,distinct)
            rows.append(dict(q=q,n=n,total=q**n,solvable=solved,unique=unique,
                             branching=solved-unique,distinct_shell_unique=distinct,
                             maximum_successful_paths=maxpaths))
            print(json.dumps(rows[-1]),flush=True)
        raw_paths.cache_clear()
        run_paths.cache_clear()
        grammar_solvable.cache_clear()
    assert reported == {'total':10350,'solvable':1567}, reported
    with (ROOT/'data/raw_counts.csv').open('w') as f:
        writer = csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n')
        writer.writeheader();writer.writerows(rows)
    with (ROOT/'data/first_move_histogram.csv').open('w') as f:
        writer = csv.writer(f,lineterminator='\n');writer.writerow(['q','n','successful_first_moves','strings'])
        writer.writerows((*key,v) for key,v in sorted(first_hist.items()))
    (ROOT/'data/shell_counterexample.json').write_text(json.dumps(observed_witness,indent=2)+'\n')
    summary = dict(raw_strings=sum(r['total'] for r in rows),
                   grammar_checks=grammar_checks,
                   reported_experiment=dict(reported),
                   failures=0,elapsed_seconds=time.monotonic()-start)
    (ROOT/'data/experiment_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)


if __name__ == '__main__':
    run()

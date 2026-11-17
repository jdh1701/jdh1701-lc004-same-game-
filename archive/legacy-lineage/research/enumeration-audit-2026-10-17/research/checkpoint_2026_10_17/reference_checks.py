#!/usr/bin/env python3
"""Check orbit polynomials against Kurz 2001 and formula algebra, exactly."""
from collections import defaultdict
from math import prod
from pathlib import Path
import csv
import json
from binary_unique_conjecture import predicted_raw_count

HERE=Path(__file__).resolve().parent
# Power-basis coefficients in increasing powers, transcribed from the primary
# two-page Kurz note. These are prior winning-word results, not discoveries.
KURZ={
 1:[0],2:[0,1],3:[0,1],4:[0,-1,2],5:[0,-4,5],6:[0,-1,-3,5],
 7:[0,15,-35,21],8:[0,23,-36,0,14],9:[0,-41,162,-204,84],
 10:[0,-161,465,-405,60,42],11:[0,12,-341,990,-990,330],
}


def run():
    data=defaultdict(dict)
    with (HERE/'data/orbit_polynomials.csv').open() as f:
        for r in csv.DictReader(f):data[int(r['n'])][int(r['k'])]=int(r['solvable_orbits'])
    checks=0
    for n,coeff in KURZ.items():
        for q in range(13):
            published=sum(a*q**i for i,a in enumerate(coeff))
            observed=sum(v*prod(q-i for i in range(k)) for k,v in data[n].items() if k<=q)
            assert published==observed,(n,q,published,observed)
            checks+=1
    u=[predicted_raw_count(n) for n in range(81)]
    for n in range(8,81):
        assert u[n]==4*u[n-1]-5*u[n-2]+u[n-3]+2*u[n-4]-u[n-5]
    result={'Kurz_2001_exact_polynomial_evaluation_checks':checks,
            'binary_weighted_formula_vs_recurrence_n8_through_80':'PASS',
            'binary_formula_coefficients_0_to_30':u[:31],
            'classification_status':'Paper proof argument; not a Lean game-counting theorem.',
            'failures':0}
    (HERE/'data/reference_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':run()

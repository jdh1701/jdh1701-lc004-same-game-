#!/usr/bin/env python3
"""Evaluate the recorded prediction with full signed witness joins at n=13."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import time
from connected_weights import witnesses,signed_constraints,nc_components

HERE = Path(__file__).resolve().parent


def main():
    path = HERE/'data/prediction_length13.json'
    predicted = json.loads(path.read_text())
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(json.dumps(dict(prediction_sha256=digest,phase='begin full n=13 computation')),flush=True)
    start = time.monotonic()
    patterns = witnesses(13)
    print(json.dumps(dict(witnesses=len(patterns))),flush=True)
    coeff,peak = signed_constraints(patterns)
    poly,conn = Counter(),Counter()
    small_blocks = []
    connected_terms = []
    for p,a in coeff.items():
        k = len(set(p))
        poly[k] += a
        if len(nc_components(p)) == 1:
            conn[k] += a
            if k > 1:
                term = dict(partition=p,coefficient=a,block_sizes=sorted(Counter(p).values()))
                connected_terms.append(term)
                if min(term['block_sizes'])<5:
                    small_blocks.append(term)
    actual = {k:a for k,a in poly.items() if a}
    expected = {int(k):a for k,a in predicted['predicted_polynomial'].items()}
    result = dict(n=13,prediction_sha256=digest,witnesses=len(patterns),
                  signed_terms=len(coeff),peak_terms=peak,polynomial=actual,
                  connected_polynomial=dict(conn),prediction_matches=(actual==expected),
                  q3=sum(a*3**k for k,a in actual.items()),
                  q4=sum(a*4**k for k,a in actual.items()),
                  small_block_counterexamples=small_blocks,
                  connected_terms=connected_terms,seconds=time.monotonic()-start)
    (HERE/'data/holdout_length13.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='connected_terms'}),flush=True)
    # A mismatch is research evidence, not an exception that destroys output.


if __name__ == '__main__':
    main()

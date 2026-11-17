#!/usr/bin/env python3
"""Record a conditional length-13 prediction BEFORE the holdout computation.

Hypothesis: every block in a nontrivial connected partition with nonzero
signed coefficient has at least five positions. Together with component
factorization this implies deg R_13(q) <= 2. Neither hypothesis is proved.
Only existing n<=12 polynomials and known one-/two-colour counts are inputs.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
from connected_weights import orbit_moments, formal_cumulants, add

HERE = Path(__file__).resolve().parent


def fib(n):
    a,b = 0,1
    for _ in range(n):
        a,b = b,a+b
    return a


def evaluate(p,q):
    return sum(a*q**k for k,a in p.items())


def main():
    n = 13
    old = orbit_moments(12)
    # With the new moment set to zero, the transform gives -K_13.
    remainder = formal_cumulants(old+[{}])[13]
    known = {k:-a for k,a in remainder.items()}
    one = 1
    two = 2**n-2*n*fib(n-2)-(-1)**n-1
    r1,r2 = one-evaluate(known,1),two-evaluate(known,2)
    assert (r2-2*r1)%2 == 0
    b = (r2-2*r1)//2
    a = r1-b
    connected = {1:a,2:b}
    predicted = add(known,connected)
    result = dict(n=n,created_utc=datetime.now(timezone.utc).isoformat(),
        status='conditional prediction; length-13 partition computation not yet run',
        assumptions=['crossing-component coefficient factorization',
                     'at least five positions per block in nontrivial connected support'],
        input_lengths=list(range(13)),one_colour=one,two_colour=two,
        connected_polynomial=connected,predicted_polynomial=predicted,
        predicted_q3=evaluate(predicted,3),predicted_q4=evaluate(predicted,4))
    path = HERE/'data/prediction_length13.json'
    if path.exists():
        raise SystemExit('Refusing to overwrite the recorded prediction.')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
    print('prediction_sha256='+hashlib.sha256(path.read_bytes()).hexdigest(),flush=True)


if __name__ == '__main__':
    main()

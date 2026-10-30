# Open-ended Python exploration environment (Claude, own initiative)

Branch: `exploration/claude-sage-20261029`. Workflow:
`.github/workflows/claude-exploration.yml`.

## Tooling choice: plain Python, not the Sage docker image

The project already runs `sagemath/sagemath` in Docker for the existing
`sage` CI jobs (`choice-complex.yml`, `coefficient-campaign.yml`) -- those
are independent-implementation controls (homology, exact arithmetic
cross-checks) where Sage's specific libraries earn their ~1GB image pull.
For this exploration track the actual computation (`rgs_symbolic_count.py`'s
restricted-growth-string DP, exact Python big integers, a plain HTTP call to
OEIS) needs none of that: no symbolic algebra, no number-theoretic library
calls, no polynomial rings beyond falling-factorial bookkeeping already done
by hand in plain arithmetic. Plain `actions/setup-python@v5` starts in
seconds versus minutes for the Sage pull, which matters more here because
the point of this track is many short iterations, not one authoritative
control run. Recommendation: keep Sage for the controls track it's already
used for; use plain Python (optionally `sympy`/`mpmath` if a future probe
needs symbolic polynomials or arbitrary-precision transcendentals) for this
open-ended track. Nothing found so far needs Sage specifically.

## What this track does

`extend_coefficient_table.py` re-derives the exact falling-factorial
coefficients c_k(n) of T(q,n) directly from the existing
`research/rgs_symbolic_count.py` grammar DP (an independent, pre-existing
ground-truth oracle in this repo, unrelated to the NC-certificate/
free-cumulant machinery everything else builds on) and dumps a JSON table.
The DP's state space grows worse than exponentially: n=15 took ~23s and
n=16 did not finish in the remaining local time budget (2 cores). The
script is time-budgeted so a CI run reports exactly how far it got rather
than hanging.

`oeis_lookup.py` then searches OEIS for every per-k column sequence
(c_k(n) for fixed k as n varies) with >=6 terms. OEIS is not reachable from
this project's own sandbox at all (proxy-restricted), so this step only
runs meaningfully in CI, which has unrestricted internet -- this is
specifically why this track belongs on GitHub rather than only locally.

## Local smoke test (n=1..15, 25s budget, confirms the oracle is sound)

```
k=1 (n=2..15): [1]*14
k=2 (n=4..15): [2, 5, 12, 28, 62, 138, 300, 649, 1386, 2938, 6174, 12888]
k=3 (n=6..15): [5, 21, 84, 300, 1005, 3300, 10511, 33189, 103467, 320970]
k=4 (n=8..15): [14, 84, 480, 2310, 10395, 44759, 185640, 755125]
k=5 (n=10..15): [42, 330, 2475, 15015, 85085, 452543]
k=6 (n=12..15): [132, 1287, 12012, 88088]
k=7 (n=14..15): [429, 5005]
```

Sanity check, not a new result: each column's first (minimal-n) entry is a
Catalan number (2, 5, 14, 42, 132, 429 = C_2..C_7), consistent with this
project's already-established NC-matching/Catalan correspondence
(`MatchingCatalan.lean`). This just confirms the independent oracle agrees
with the existing theory at the boundary where the two overlap -- it is not
itself new information.

## Status

VERIFIED-COMP (oracle behavior only). No OEIS match or closed-form pattern
beyond the already-known Catalan boundary identified yet; the CI run with a
larger time budget and the OEIS search pass had not completed as of this
writing. This is genuinely open-ended exploration and may turn up nothing
further -- reporting that plainly if so, rather than reaching for a claim.

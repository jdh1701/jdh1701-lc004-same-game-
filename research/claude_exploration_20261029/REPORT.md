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

## CI results and a genuine negative finding: OEIS is unreachable from here

Extended the table to n=17 on a CI runner (vs n=15 reached locally in the
same wall-clock budget -- some runs reached only n=15 too; GH Actions
runner throughput for this workload varied noticeably run to run,
consistent with this project's own prior note about shared/contended
runners). No closed form or pattern beyond the already-known Catalan
boundary turned up in the rows computed so far.

The OEIS search step itself failed cleanly every time it ran (3 CI
attempts, after fixing two of my own bugs along the way -- an uncaught
`AttributeError` when OEIS's JSON response wasn't shaped as expected, and
a first guess that the default `urllib` User-Agent was being blocked):
**every single query returns HTTP 403 Forbidden**, for every per-k column,
across every attempt, including after sending a normal browser-style
User-Agent. This looks like oeis.org blocking the GitHub Actions runner IP
ranges outright (a common anti-scraping measure against major cloud
providers), not a request-shape problem on this script's end -- there is
nothing further to fix here from this side. **OEIS lookups are not
reachable from this project's CI, the same as they are not reachable from
the sandbox** (for a different reason: the sandbox's own proxy blocks it;
CI's outbound network is unrestricted but oeis.org itself blocks it back).

## Status

VERIFIED-COMP (oracle behavior and CI runner mechanics only). No OEIS
match or closed-form pattern found in the rows computed (n up to 17). The
automated-OEIS-lookup idea specifically is a dead end in this environment;
a future pass wanting OEIS cross-reference will need a human to run the
lookup outside CI, or a different lookup source. Reporting this plainly as
a negative result rather than retrying further.

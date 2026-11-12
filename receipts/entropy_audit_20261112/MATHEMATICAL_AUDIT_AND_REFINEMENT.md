# Independent implementation and exact common-bias refinement

## New computational evidence

A separately written `independent_lift_check.py` uses integer tuples, explicit permutations and Python Fraction arithmetic. It imports no original checker/model-generator code. It passed 416,322 semantic checks: the original two representative bases plus all four proper length-three bases ending in color zero, adding 277,548 deeper-base tests. All 46,258 drift inequalities pass. This is implementation diversity by another audit pass, not an independent external researcher and not a formal arbitrary-depth proof.

## A stronger certificate using the same potential

For each state/context let d_a be the integer-scaled potential increment, S=sum_a d_a, and f the increment for the fixed favored color. A conditional law proportional to (1+e,1,1) has negative expected drift exactly when S+ef<0. Intersecting all 46,258 strict rational inequalities gives the feasible open interval

    45248935/410282362 < e < 10996525/97447751.

The lower endpoint is attained by state 736, context 0; that row has S=45,248,935 and f=-410,282,362. Therefore the previous e=1/9 is not the least possible common bias for this already-known potential. This observation needs no new numerical optimizer.

Choose e=11028731/100000000, strictly inside the feasible interval. The weights are now (111028731,100000000,100000000), denominator 311028731. Both checkers pass the new certificate. The worst scaled drift is -304,542,622 over 31,102,873,100,000,000, strictly negative.

The same finite-support invariant, boundary policy, drift argument and entropy counting argument in the original REPORT.md apply with these weights. Thus, conditional on that paper argument and the fusion-to-game bridge, the improved lower bound is

    311028731 / (111028731^111028731 * 100000000^200000000)^(1/311028731)

approximately 2.9962726127823. The exact expression is authoritative. `check_rate_interval.py` additionally proves with rational logarithm-series bounds that it lies strictly between 2.99627261278230836 and 2.99627261278230838; this enclosure does not use floating-point arithmetic. The old certificate is preserved unchanged. The improvement is small (about 0.00005356), and is not an exact enumeration formula. It is an optimization of this fixed certificate, not a globally optimal potential or policy. The much smaller drift margin also worsens the conservative finite-size constants in the tail proof.

## Paper proof audit

1. **Arbitrary-base lifting:** Every accepted witness preserves all but the last base letter. Writing a long base as P b 0, each one-step stack successor is P times the corresponding representative successor because a proper stack step only changes its final letter. Prepending P therefore transports a subset witness. The required target nonemptiness, properness and base compatibility are checked. The longer-base tests corroborate this argument but do not replace it.
2. **Boundary:** When the base has length 0 or 1, choose one genuinely reachable retained stack and one legal next-step successor. Its length is at most H+2; encode it as base with empty suffix control. All future input probabilities remain bounded below by low/(high+2 low).
3. **Tail bound:** The bounded-increment negative drift applies only outside the boundary. The separate boundary upper bound gives E[V_{t+1}] <= rho E[V_t]+D, hence a uniform exponential moment bound. Constants can be extremely large but finite, which is sufficient for an asymptotic statement.
4. **Completion:** A retained proper stack can be popped by reading its reversal. A monochromatic block of any prescribed remaining length at least two can then be erased. This makes the finishing suffix length fixed, including an empty chosen stack. The policy need not retain the accepting path during completion; existence in the genuine fusion support is sufficient.
5. **Entropy:** The favored physical color is a deterministic function of past input. Each conditional distribution is a permutation of the same three weights; the conditional entropy is constant. The bounded martingale difference estimate controls information fluctuations without assuming independent letters. Combining positive tilted winning probability with the high-information event gives the unweighted count bound.

No contradiction was found in these steps. They remain paper arguments, not newly Lean-compiled theorems. Formal obligations are (a) finite-table lifting and policy induction, (b) boundary repair and a uniform moment lemma, (c) exact-length completion, (d) the conditional-information martingale counting lemma, and (e) the connection to the pinned original-game soundness theorem. Finite-checker success alone discharges none of these general analytic obligations.

## Focused literature check, not priority certification

Searches used `"same game" ternary "growth"`, `"A035617" asymptotic`, `"one-dimensional" "samegame" probability`, `Clickomania one column random strings asymptotic winning probability`, and `"same game" "entropy" winning strings`.

- OEIS A035617's retrieved entry describes ternary winning words and states in a 2018 comment that the b>=3 counting problem appears unsolved. This is a historical catalog comment, not proof that no subsequent asymptotic result exists: https://oeis.org/A035617/internal
- Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, *The Complexity of Clickomania* (2001), arXiv abstract inspected, gives polynomial-time one-column recognition for arbitrary colors. Recognition of an individual word is not enumeration of all winning words or an asymptotic density result: https://arxiv.org/abs/cs/0107031
- Burns/Purcell's journal PDF was reachable but did not yield readable text through the reader in this pass. No new full-paper literature-review claim is made: https://www.fq.math.ca/Papers1/45-3/burns.pdf
- Kurz's OEIS-hosted paper returned 403 in this pass: https://oeis.org/A035617/a035617.pdf

These limited searches found no directly matching ternary entropy-bound result, but do not establish novelty. Full-text review of Kurz, Burns/Purcell, later citations and related random-word deletion languages remains necessary before asserting priority. The general drift/entropy techniques are not claimed new.

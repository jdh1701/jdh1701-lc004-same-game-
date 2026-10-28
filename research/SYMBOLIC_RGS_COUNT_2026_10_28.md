# Symbolic Same Game counting polynomials by restricted-growth parser states
Date: 2026-10-28
Status: EXACT for the displayed pair/triple grammar; independently checked against ordinary Same Game through n=10. NOT a proof of all-n grammar/game equivalence or an established new bibliographic result.

## Representation and invariant
Let a(n,k) count distinct accepted color-isomorphism patterns of length n using exactly k colors. Every such pattern has a unique restricted-growth encoding: the first color is 0, and the next symbol is among colors seen previously or the new color k. For the pair/triple grammar, each color used must occur at least twice, so k<=floor(n/2). Each accepted restricted-growth pattern has exactly (q)_k distinct labelings into q colors, hence W_n^G(q)=sum_k a(n,k)*(q)_k, where (q)_k is the falling factorial and W^G counts distinct grammar words.

A deterministic state is (F,k), with F a set of viable parser stacks after a restricted-growth prefix and k its number of introduced colors. The next letter has only k+1 possible normalized choices (or k if all Q colors introduced). Every normalized prefix follows exactly one deterministic state path; merging identical (F,k) and summing prefix multiplicities counts each color pattern ONCE, regardless of ambiguous grammar derivations. For a target length n, run the parser over Q=floor(n/2) colors so there are enough unused colors for all possible accepted patterns.

This avoids enumerating q^n labeled words and computes ALL coefficients of the grammar counting polynomial in one execution. It does NOT establish asymptotic polynomial-time complexity. Automata determinization and restricted-growth strings are established techniques; specific all-n novelty remains to be assessed against Kurz (2001) and other primary literature.

## New actual computations
n=12, Q=6: coefficients a(n,k) for k=1..6:
[1,1386,10511,10395,2475,132], peak 682 deterministic (F,k) states, 2156 distinct closures, ~0.39 sec.
n=13, Q=6:
[1,2938,33189,44759,15015,1287], peak 2088 states, 6589 closures, ~1.39 sec.
n=14, Q=7:
[1,6174,103467,185640,85085,12012,429], peak 4256 states, 14723 closures, ~5.97 sec.
n=15, Q=7:
[1,12888,320970,755125,452543,88088,5005], peak 15097 states, 50761 closures, ~19.43 sec.

Evaluating the resulting length-15 polynomial at q=3 gives 2,003,151, matching the published ternary sequence, and at q=4 gives 25,980,940 (an exact result for the grammar; universal original-game identity remains conditional).

## Independence tests
For all n=2..10, Q=floor(n/2), exhaustive enumeration of ALL restricted-growth patterns and an independent recursive MAXIMAL-RUN SAME GAME solver produced identical coefficient dictionaries. These comparisons do not use the grammar parser as the reference predicate. Tests passed:
n2 {1:1}; n3 {1:1}; n4 {1:1,2:2}; n5 {1:1,2:5};
n6 {1:1,2:12,3:5}; n7 {1:1,2:28,3:21};
n8 {1:1,2:62,3:84,4:14}; n9 {1:1,2:138,3:300,4:84};
n10 {1:1,2:300,3:1005,4:480,5:42}.

## Separate fixed-q length-17 success and previous timeout
The previous q=3 n=17 color-orbit parser, rerun with enough time, completed in 101.236 seconds:
count=18,624,693, peak=9,510 orbit states, 110,538 transitions, 44,216 closure states. This agrees with OEIS A035617. An earlier 180-second run timed out; retaining both demonstrates runtime variability rather than a mathematical discrepancy. n=16 completed previously in 33.198 seconds.

## Adversarial limitations
1. Strongest theorem not yet formally proved: equivalence of pair/triple CFG membership with winning in the ORIGINAL maximal-run Same Game for all lengths and colors. The symbolic count is therefore for the grammar, with finite agreement for the game.
2. No general closed form or finite-order recurrence for coefficients a(n,k) was found; the algorithm constructs possibly exponentially many distinct parser states.
3. The leading coefficients recover Catalan and triple-block binomial families, already suspected; priority claims require literature.
4. Counting all falling-factorial coefficients at once is a concrete algorithmic improvement over previous fixed-q results, not automatically a resolution of the open enumeration question.
5. Peak state counts exclude the sizes of stack sets INSIDE states and their caches; they are not a fair total memory estimate. Report runtime and memory in future profiling.

## Next discriminatory program
- Formalize grammar ↔ raw-game winning in Lean, especially maximal run semantic equivalence.
- Derive recurrences for a(n,k) directly from smaller symbolic states without building full parser-set powersets.
- Audit published Kurz polynomial coefficients against this table and check any higher n for novelty.
- Run held-out q=4 checks independent of the grammar to distinguish implementation and theory.

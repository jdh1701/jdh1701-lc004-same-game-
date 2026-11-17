# Trace-quotient test (2026-10-29)

Follow-up to `CONSOLIDATION.md` §5: does quotienting successful deletion paths
by commutation of independent moves compress the branching class B enough to
give a canonical, non-overcounting description of winning words?

Exact, exhaustive over labeled ordinary words for q=2 n≤14, q=3 n≤11,
q=4 n≤9. Finite evidence only, not proofs.

```sh
python3 trace_census.py --ranges 2:14,3:11,4:9 > results/trace_census.jsonl
python3 canonical_scheme.py --ranges 2:14,3:11,4:9 > results/canonical_scheme.jsonl
```

## Definitions

A move is identified by the set of **original cell positions** it deletes.
For a winning word:

- **P**: number of successful deletion paths.
- **K**: number of *schemes*, i.e. sets of blocks deleted by some successful
  path, ignoring order.
- **T**: number of trace classes, i.e. components of successful paths under
  swapping two adjacent moves when the swapped sequence is still successful.

Winning counts W reproduce OEIS A035615 (q=2) and A035617 (q=3).

## Results

**1. Trace classes = schemes.** `T = K` for every winning word in range
(0 exceptions). Every scheme is a noncrossing partition of the positions
(0 exceptions; crossing is in fact impossible, since each of two crossing
blocks would have to be deleted before the other).

*Conjecture (T = K):* all successful orders of one scheme are connected
by adjacent transpositions. The order constraints are not a poset (in
`aabbaa` with blocks `aa | bb | aa`, `bb` needs *at least one* `aa` removed
first), so this is not just "linear extensions are swap-connected".

**2. The quotient compresses B a lot, but not asymptotically.**

| q | n | W | P = 1 | K = 1 | K = 1 share |
|---:|---:|---:|---:|---:|---:|
| 2 | 10 | 602 | 158 | 422 | 70.1% |
| 2 | 14 | 12350 | 1370 | 5004 | 40.5% |
| 3 | 9 | 2631 | 537 | 2241 | 85.2% |
| 3 | 11 | 23697 | 2709 | 18039 | 76.1% |
| 4 | 9 | 10876 | 1792 | 9688 | 89.1% |

Most path multiplicity is just reordering of independent moves. For example
at q=3, n=11 only 11.4% of winners have one path, but 76.1% have one scheme.
The K = 1 share still falls steadily with n, and the maximum K grows (q=2,
n=14 reaches K = 20). The full distributions are in
`results/trace_census.jsonl`.

**3. Residual ambiguity is same-color regrouping.** Blocks are monochromatic,
so two schemes of a word can differ only in how the cells of each color are
grouped. The first K > 1 word is `aabbaa`: `{aa, bb, aa}` versus `{bb, aaaa}`.

**4. No size-based canonical scheme (negative).** `canonical_scheme.py` tests
whether the finest (most blocks) or coarsest (fewest blocks) scheme is unique
and comparable with all others. Both fail from n = 8 for every q tested:

- `abbaabba`: two 3-block schemes, `{0,7 | 1,2,5,6 | 3,4}` and
  `{0,3,4,7 | 1,2 | 5,6}`, neither refining the other. No unique finest scheme.
- `aabbaabb`: coarsest schemes `{0,1,4,5 | 2,3 | 6,7}` and
  `{0,1 | 2,3,6,7 | 4,5}`. No unique coarsest scheme.
- `aabbaabba`: the unique finest scheme does not refine all others.

## Consequence for enumeration

Σ K over words (word–scheme pairs) is a noncrossing-partition count with
color and realizability constraints, plausibly grammar-countable. W is the
number of words with K ≥ 1. Closing that gap needs one of:

1. a canonical scheme chosen by a positional rule (e.g. greedy
   leftmost-block or nesting-based), proved unique; or
2. an inclusion–exclusion / Möbius correction over the regrouping relation
   among schemes of a word.

Size-based canonical choices are ruled out by item 4. The next test is
whether some positional rule picks exactly one scheme per winning word and
is locally checkable.

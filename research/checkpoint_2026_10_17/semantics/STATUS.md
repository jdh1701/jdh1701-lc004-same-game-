# Ordinary-word semantics and higher-order ambiguity

Continuation from `c3f2a4fdb5ae9c34e53fd37782e40eb6001908ac` on the existing
research branch. The user explicitly authorized continued uploads.

## The semantic gap is closed

`LC004/OrdinaryCorrespondence.lean` preserves the independently specified
cell-deletion function from the older research branch, including its fuel
and maximal-run `takeWhile`/`dropWhile` implementation. It was previously
accompanied only by transfer theorems conditional on a commuting assumption.
`LC004/OrdinaryCommutation.lean` now proves that assumption:

```lean
theorem ordinaryStepAt_map_encode (w : RawState) (i : Nat) :
    (ordinaryStepAt w i).map encode = stepAt (encode w) i
```

This is a universal equation for every raw word and every run index,
including illegal indices and singleton runs. The proof establishes the
exact first-run decomposition, the effect of prepending a constant run,
preservation of the first colour by a later deletion, and sufficient fuel.
It does not define raw deletion by invoking the Boolean solver.

`LC004/OrdinaryFinal.lean` consequently proves, without a remaining semantic
assumption:

* ordinary successful index sequences are exactly the encoded successful
  index sequences;
* ordinary solvability agrees with run-state solvability;
* for a nonempty ordinary word, unique successful first move iff unique
  complete path;
* the unique path is `[m,m-1,...,0]` for `2m+1` encoded runs, and the encoded
  colour skeleton is palindromic;
* the certified finite path enumerator counts ordinary indexed paths;
* equal encodings preserve the entire set of successful index sequences
  and its cardinality;
* expanding light runs to one cell and heavy runs to two cells recovers
  every normalized state exactly, so the transfer works in both directions.

The empty word is retained and has one empty successful path. Uniqueness
of the first move still requires a nonempty source. Clicks on different
cells of the same maximal run do not constitute different paths.

The stronger pointwise claim about an arbitrary *exact successor word*
remains false: deleting the first run of `0011` yields `11`, not `111`,
although both successors have the same encoding. Negative controls are
included in `PrintAxioms.lean`.

## The search can prune ambiguous supersets soundly

`LC004/PathMonotonicity.lean` proves `stepAt_heavier` and
`successfulPath_heavier`: upgrading singleton flags to heavy flags preserves
each successful path with exactly the same run indices. Thus solution sets
are included and their cardinalities cannot decrease. In particular,
ambiguity is upward closed. A solvable lighter state below a unique state
is unique.

This justifies looking for inclusion-minimal ambiguous flag subsets. It
does not place a bound on their sizes or certify a particular Python
implementation by extraction.

## New discriminating computations

The antichain search exhausts first-occurrence colour representatives of
normalized palindromic skeletons with at most three colours, a heavy centre,
and one through eight shells (3 through 17 runs). It grows unique subsets
one flag at a time and evaluates a candidate only when all its immediate
subsets are unique. Every skipped ambiguous superset is excluded by the
monotonicity argument. Reversal is not quotiented.

At eight shells there are 128 colour representatives. The search evaluates
531,194 nonempty flag candidates; 528,376 are unique. Its minimal ambiguous
sets have the following sizes:

| Optional heavy runs | Number at eight shells |
|---:|---:|
| 2 | 1,692 |
| 4 | 1,104 |
| 5 | 6 |
| 6 | 16 |

This search took about 523 seconds for all shell sizes. These are finite
counts of flag obstructions, not counts of all winning words.

Two representative obstructions use 17 runs. The six-run one has colour
half `010212010` and optional positions `1,3,6,9,11,14`; the five-run one
has half `012010102` and optional positions `2,3,7,10,12`. In both, the centre
at index 8 is heavy. The full skeleton is `half ++ reverse(half.dropLast)`.

Independent raw-cell and exact run solvers check every mask in both
examples, 96 mask cases in total. Every proper subset has one solution.
The full six-run example has **9,451** solutions; the full five-run example
has **1,681**. Those exact full counts are Python results. The Lean
certificates concern uniqueness of all proper subsets and nonuniqueness of
the full subsets, without evaluating all 9,451 or 1,681 paths in the kernel.

`LC004/HigherObstructions.lean` certifies these properties in Lean. It
computes the exact singleton path sets of just the five/six maximal proper
subsets using kernel `decide`, then applies the proved monotonicity theorem
and a checked canonical successful path to cover all 31/63 proper subsets.
Two explicitly checked index sequences disprove full-mask uniqueness.
The corresponding raw-word uniqueness and nonuniqueness statements follow
from the unconditional encoding theorem, using `expandRuns` representatives.

## A candidate family, not a universal theorem

The six-run witness suggested this precise family. For `k>=1`, concatenate
`k` alternating blocks `010,212,010,212,...` to form the colour half. It has
`3k` entries; form `half ++ reverse(half.dropLast)`. The resulting
skeleton has `6k-1` runs. Make the centre `3k-1` heavy. The `2k` optional
heavy positions are

```text
{1} union {3j : 1 <= j < k}
union {3k} union {3k+2+3j : 0 <= j < k-1}.
```

The conjecture is: all options together are ambiguous, while every proper
subset has exactly one solution. `chain_family.py` checks the full state
and every maximal proper subset for **k=1,...,7**, giving interaction sizes
2,4,6,8,10,12,14 and run counts 5,11,17,23,29,35,41. All pass, in about 24
seconds. Monotonicity plus the canonical successful path reduces all proper
subsets to these maximal ones. The Python checks do not prove the assertion
for arbitrary k. The k=1 member uses two colours; all later members use
three.

## Strategy change and remaining problem

The four-way result was not the end of the interaction hierarchy. The
six-way obstruction rules out a forbidden-subset characterization using
only sets of size at most five. The five-way example also rules out the
guess that minimal interactions always have even size. The candidate
family gives a concrete induction target for unbounded interaction size
with only three colours.

Accordingly, further large raw-word censuses and attempts to fit a bounded
local-conflict rule are lower priority. The next structural target is an
inductive proof or falsification of the displayed family, especially the
assertion that removing any one optional heavy run forces the median path.
If established, a counting method must retain context of unbounded size or
compress it by a proved recursive rule. This does not rule out efficient
algorithms with richer states or an unambiguous recursive decomposition.

The full enumeration of winning words for q>=3 remains unresolved. The
binary unique-word generating function still lacks a universal Lean
counting proof. The finite family evidence and semantic bridge do not
constitute a solution to either counting problem. No new mathematical
priority claim is made; the previous source register remains applicable.

## Verification and reproduction

Pinned Lean 4.19.0 and the committed dependency manifest are unchanged.
Local verification uses the documented process-path compatibility wrapper;
it changes executable-path discovery, not the kernel or theorem statements.
Failed proof attempts are retained under filenames containing `attempt`.
Error-recovery `sorryAx` output in a failed attempt is not a certificate;
the final successful build and final axiom report are the relevant evidence.
The root build imports the new formal modules. GitHub Actions performs a
normal-runner build without the local compatibility wrapper.

The final local root build exited 0. The static audit covers all 79 project
Lean source files; 74 modules are in the root import closure. It found no
proof holes, project axiom declarations, unsafe overrides or native
computational tactics. Principal theorem axiom reports use only subsets of
`propext`, `Classical.choice`, `Quot.sound`. The raw commuting theorem needs
only `propext` and `Quot.sound`; indexed path monotonicity needs only `propext`.
The previous published base independently passed GitHub Actions run
39026532662. Verification of this new publication must be read from its own
workflow run, not inferred from that earlier result.

```sh
lake exe cache get
lake build
lake env lean research/checkpoint_2026_10_17/semantics/PrintAxioms.lean
python3 research/checkpoint_2026_10_17/semantics/check_witnesses.py
python3 research/checkpoint_2026_10_17/semantics/chain_family.py --kmax 7
python3 research/checkpoint_2026_10_17/semantics/obstruction_search.py --q 3 --mmax 8
python3 research/checkpoint_2026_10_17/semantics/audit.py
```

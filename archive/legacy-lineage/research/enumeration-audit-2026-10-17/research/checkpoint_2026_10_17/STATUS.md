# Same Game research checkpoint — 17 October 2026

**Subsequent extension:** [canonical/STATUS.md](canonical/STATUS.md) records
the proved complete index sequence, certified finite path enumerator,
four-way ambiguity certificate, and longer multicolour unique-word counts.
This checkpoint was published as `25963923aa96a21bfc685b25c125d7dd94a7e16d`
and passed normal GitHub Actions run 39025601875.

The existing uniqueness theorem was independently rebuilt. New median and
colour-palindrome necessity theorems were checked by Lean. A binary unique-word
counting formula now has an explicit paper proof argument and strong finite
checks, but is **not a Lean game-counting theorem**. The general q>=3 winning
enumeration problem remains unresolved by this work. Mathematical priority
has not been established for the new structural statements or counting formula.

## 1. Independently reproduced baseline

Repository: `jdh1701/jdh1701-lc004-same-game-`.
Baseline commit: `a9cb335c11b795372b7a4d22b68c6c4fab83239c`.
Pinned Lean: 4.19.0, release commit `6caaee842e94`.
Pinned Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The clean baseline was built in a detached worktree, with no tracked source
changes and a fresh project build directory. The actual command was
`LD_PRELOAD=/tmp/samegame-proc-self-compat.so lake build`.
The small compatibility wrapper only translates the current-process
executable path lookup; its exact source and environment qualification are
in README. Dependency binaries came from the normal pinned Mathlib cache.
The build exited 0. Literal output is `logs/baseline_clean_build.log`.

Both existing capstones reported exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This reproduces the theorem about normalized nonempty Boolean run states.
It does not establish bibliographic priority or automatically prove the
ordinary-cell/Boolean commuting theorem.

The historical Python campaigns also exited 0:

| Campaign | Exhaustive domain / observed outcome |
|---|---|
| `scripts/exhaustive_verify.py` | 797,161 ternary raw words through n=12; 524,286 normalized ternary states through 9 runs; zero failures |
| `research/exhaustive_structure.py` | 489,538 canonical run states across its q=3,4,5 ranges; 1,002 unique-first cases and 1,163,048 exchange cases; zero failures |

These domains overlap. They must not be added as counts of independent evidence.

## 2. New Lean statements actually checked

File: `LC004/UniqueMedian.lean`; imported by the default `LC004.lean` root.
The root import closure now has 66 project modules. Text scans also covered
the other project Lean source files, which should not be described as all
compiled merely because the default target passed.

For **normalized, nonempty** `s : List (Nat × Bool)`:

| Declaration | Mathematical content | Additional hypotheses |
|---|---|---|
| `unique_successful_choice_is_median` | A successful choice in a unique-first state has index i with `s.length = 2*i+1` | Relational unique successful choice and a successful witness |
| `unique_successful_first_is_median` | Same conclusion for the executable selected index | `UniqueSuccessfulFirst s`, `SuccessfulMove s i` |
| `unique_successful_path_odd_runs` | Unique successful path implies an odd number of runs | `UniqueSuccessfulPath s` |
| `unique_successful_path_color_palindrome` | The run-colour list equals its reverse | `UniqueSuccessfulPath s` |

There is no upper bound on palette size in these theorems. Symmetry concerns
the **colour skeleton**; neither Boolean flags nor raw run lengths are claimed
to be symmetric. A palindromic skeleton is a necessary, not sufficient,
condition for uniqueness.

The proof uses the existing proved critical-pair exchanges, strong induction
on run count, and the fact that the unique bridge child's only successful
index is the newly merged run. The median equation balances the two contexts;
induction then forces the colour-palindrome identity.

Final root build: exit 0 (`logs/research_build_final.log`). Each principal
new theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
The independent print command and complete declarations are in
`logs/print_axioms_final.log`; reproduce with `PrintAxioms.lean`.

The first build attempt failed on a redundant simplification. That failed
log contains Lean's **error-recovery** `sorryAx` dependencies and exit 1.
It is preserved as a failed attempt, not evidence of verification. The
corrected final build and final axiom print contain no `sorryAx`.
Final project source scans found no `sorry`, `admit`, `sorryAx`, custom axiom
declarations, unsafe/extern overrides or `native_decide`.

## 3. New computations actually executed

1. **Independent exact raw and run solvers:** 208,721 labelled words total,
   over q=2,n=0..14; q=3,n=0..10; q=4,n=0..8. They agree on exact path
   counts, every legal index and every encoded successor. The reported
   10,350 nonempty q=2,3 words through n=8 reproduce exactly, with 1,567
   solvable words. A third solver implementing the published grammar agrees
   on all 10,352 q=2,3 words through n=8, including the empty word for each q.

2. **Palette-orbit polynomials:** exact solvable and unique-path coefficients
   in the falling-factorial basis through n=12. No reversal quotient or
   interpolation is used. Singleton global colour classes are excluded only
   because they cannot be removed. All direct-count overlaps agree. The
   winning polynomials pass 143 integer evaluations of Kurz's n=1..11
   polynomials. This reproduces known palette polynomiality.

3. **Distinct-shell subclass:** 21,845 heavy-median flag assignments through
   15 runs, plus direct raw-word cross-checks. The weighted formula is in
   `BINARY_UNIQUE_COUNTING.md`. This is a strict subclass for repeated colours.

4. **Binary classifier:** all 1,398,101 heavy-median flag assignments through
   21 runs, and all 491,520 raw words of lengths 15–18. The proposed
   classification and weighted formula have zero mismatches. The held-out
   unique raw counts at lengths 15–18 are 2278, 3760, 6172, 10090. The first
   of these also reproduces a count on the older post-theorem research branch.
   Algebraic agreement between weighted expansion and the proposed fifth-order
   recurrence was checked through n=80; this is **not** game enumeration to 80.

All experiments are exhaustive in their stated domains; none is random
sampling. Exact data, literal logs and reproduction commands are included.

## 4. Failed hypotheses and repaired scope

* Palindromic colours plus at most one heavy run per mirror pair do not
  suffice. The minimal run-length failure found is seven runs. A raw witness
  is `0100110110`, whose successful paths are `[2,1,1,0]`, `[2,3,1,0]`,
  `[3,2,1,0]`, `[5,2,1,0]` (current run indices).
* The shortest solvable-prefix rule can leave an unsolvable suffix; even a
  run-boundary split fails for `00110 = 00 | 110`.
* Leftmost legal deletion fails on `00110`; the successful path is `[1,0]`.
* Rotating `0110` to `1100` changes one successful path into two. Rotation
  invariance of solvability cannot be used to quotient unique-path counts.
* A context-free grammar recognizes solvability but its derivations are not
  unique word representations. The earlier branch already documents that
  issue; it is not newly discovered here.

## 5. What the binary formula does and does not establish

The proposed classifier is precise, its full paper argument is written,
and its generating function is derived from independent run-expansion
weights. The formula for **nonempty unique-path binary words** is

```text
U_2(z) = 2z²(1-3z+3z²-2z⁴+2z⁵) / ((1-z)³(1-z-z²)).
```

It uses the known binary checkerboard obstruction and even-split theorem,
and the new median necessity result. It concerns a different counting target
from Burns–Purcell's known count of **all** winning binary words.
The game classification and formula have not been formally verified or
independently reviewed. They remain a candidate exact result for review,
not an established novelty claim. The executable retains its conservative
conjecture label so finite tests are never promoted into a proof by logging.

## 6. Novelty and unresolved objective

The search and source-access register identifies what was actually read,
the close binary median precedent, and prior polynomial results. No exact
match for the new necessity statements or binary unique-path formula was
identified in this directed review. That does not settle mathematical priority.
The Lean code is a new formalized structural extension in this repository;
some numeric values are reproductions of earlier project results.

**Full q>=3 winning-string enumeration: NOT RESOLVED.** No canonical
non-overcounting decomposition of all branching states was established.
**Ordinary-cell / Boolean-state unconditional Lean transfer: NOT PROVED HERE.**
The existing conditional module on the older branch does not close that gap.

The most informative next step is to review and formalize the binary
classification proof while separately completing the raw/Boolean commuting
equation. For q>=3, test whether the repeated-colour branching obstruction
admits a bounded description that survives context merges. This checkpoint
does not claim a fixed transfer matrix from a growing state cache.

## 7. Artifacts and publication

Research branch: `research/enumeration-audit-2026-10-17`, based directly on
`a9cb335c11b795372b7a4d22b68c6c4fab83239c`. Other branches were inspected and
preserved. The exact deliverable commit is the commit containing this file;
the final conversation report identifies its confirmed SHA. No merge into
main or force-push is required.

Principal paths:

* `LC004/UniqueMedian.lean`
* `research/checkpoint_2026_10_17/PrintAxioms.lean`
* `research/checkpoint_2026_10_17/BINARY_UNIQUE_COUNTING.md`
* `research/checkpoint_2026_10_17/SOURCE_AND_NOVELTY_REGISTER.md`
* `research/checkpoint_2026_10_17/data/`
* `research/checkpoint_2026_10_17/logs/`
* `research/checkpoint_2026_10_17/reproduce.py`
* `lake-manifest.json`

The GitHub workflow checks the research branch and pull requests on a normal
runner, imports the new proofs through the default build, and reruns the
independent solver and orbit checks. A configured workflow is not itself a
completed remote verification; inspect the actual run result separately.

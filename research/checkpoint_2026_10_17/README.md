# Reproducing the 17 October 2026 checkpoint

Read `STATUS.md` for the actual outcome, and `SOURCE_AND_NOVELTY_REGISTER.md`
before interpreting any novelty claim. `BINARY_UNIQUE_COUNTING.md` contains
the candidate binary classification, proof argument, and weighted formula.

## Game and counting conventions

Raw words have labelled colours, indexed from 0. Empty input is solvable and
has one empty successful path, but has no successful first move. Every legal
move removes a **maximal** equal-colour run of at least two cells. The two
exposed neighbours merge if equal. Two successful paths differ when their
sequences of **current run indices** differ. Clicking different cells in the
same maximal run does not create extra paths. The line has no wraparound.

Boolean run abstraction remembers colour and whether length is at least two.
The Python tests compare every legal index and encoded successor, not just
sets of successor states, and compare exact path counts. A formal commuting
theorem from ordinary cell deletion to this quotient remains outstanding.
Existing `encode_normalized` alone does not establish that theorem.

Colours are canonicalized in first-occurrence order only in orbit experiments.
A representative using k colours has exactly `(q)_k` labelled realizations:
an injection from its k ordered colour classes into the q labels determines
one realization, and each labelled word determines exactly that injection.
The move rule only uses colour equality, so injective relabelling induces
the same indexed game tree. Reversal is not included in this quotient.

For a run state with l light and h heavy runs, raw-word weight is
`z^l (z²/(1-z))^h`. At raw length n the coefficient is
`binomial(n-l-2h+h-1,h-1)` when h>0 and n>=l+2h. When h=0 it is one only
at n=l. This follows by assigning independent nonnegative extra lengths to
the h heavy runs. Counting each Boolean state with weight one is incorrect.

## Standard environment

Use Lean `leanprover/lean4:v4.19.0` and the committed `lake-manifest.json`.
Python scripts require only the standard library. From the repository root:

```sh
lake exe cache get
python3 research/checkpoint_2026_10_17/reproduce.py
```

The runner records command argument arrays, literal combined stdout/stderr,
exit codes and elapsed times. It stops on a failure. It runs the root build,
prints the actual declarations and axiom dependencies, runs the historical
Python campaigns, and runs the new experiments. Data and runtime logs are
regenerated, so their timestamps/runtime fields can change.

Individual commands:

```sh
lake build
lake env lean research/checkpoint_2026_10_17/PrintAxioms.lean
python3 scripts/exhaustive_verify.py
python3 research/exhaustive_structure.py
python3 research/checkpoint_2026_10_17/experiments.py
python3 research/checkpoint_2026_10_17/orbit_experiments.py
python3 research/checkpoint_2026_10_17/hypothesis_tests.py
python3 research/checkpoint_2026_10_17/binary_unique_conjecture.py
python3 research/checkpoint_2026_10_17/reference_checks.py
python3 research/checkpoint_2026_10_17/source_audit.py
```

## Actual host compatibility used during discovery

This host allows `/proc/self/exe` lookup but denies the equivalent
`/proc/<own numeric pid>/exe` lookup. Official Lean 4.19.0 uses the numeric
form to find its installation. The 16-line `proc_self_compat.c` wrapper
redirects **only that current-process lookup** to `/proc/self/exe`, then calls
the original `readlink`. It does not implement proof checking or modify Lean
source, declarations, axioms or the game model. The local Lean builds in this
checkpoint used this wrapper; do not omit that qualification when describing
their provenance. The GitHub workflow uses a normal runner without it.

Rebuild the wrapper only on a host exhibiting that specific failure:

```sh
cc -shared -fPIC research/checkpoint_2026_10_17/proc_self_compat.c -ldl -o /tmp/samegame-proc-self-compat.so
LD_PRELOAD=/tmp/samegame-proc-self-compat.so lake build
```

The installer/cache tar archives also included ownership metadata unavailable
on this host; extracting with `tar --no-same-owner` resolved it. The cache
helper's executable was placed at its expected versioned filename. Failed
setup logs and the interrupted pre-cache build were preserved, not relabelled
as successful verification. The final clean baseline build is separately
logged in `logs/baseline_clean_build.log`.

## Fresh historical baseline

An isolated detached worktree was created at
`a9cb335c11b795372b7a4d22b68c6c4fab83239c`. It shares only the downloaded
dependency packages with the research checkout, and has its own generated
project build directory. That project directory was removed before the clean
baseline build. No existing LC004 project `.olean` was supplied as evidence.
Mathlib binaries were the normal cache for the manifest's pinned revision.

The root research build now imports `LC004.UniqueMedian`, so a successful
default build necessarily checks the added structural theorems. The source
audit records the root import closure, all project Lean SHA-256 hashes,
manifest hash and explicit scans. A text scan supplements, rather than
replaces, the compiler's axiom output and a semantic review.

## Failed ideas retained

* Independent mirror flags on a palindromic skeleton are insufficient: the
  ten-cell word in `data/shell_counterexample.json` has four successful paths.
* Shortest solvable prefix splitting can leave an unsolvable suffix.
* Leftmost legal greedy deletion can lose a solvable position.
* Rotation preserves binary solvability in the cited paper, but does not
  preserve the number of successful paths: `0110` has one and `1100` has two.
* General palette polynomiality and a context-free recognizer are already
  in the cited literature; they are not newly solved problems.

## Precise next targets

1. Check the binary paper argument independently, then formalize its
   checkerboard obstruction and even-split inputs against `IndexedStep`.
2. Prove the ordinary-word / Boolean-state commuting equation rather than
   an overstrong pointwise relational iff that forgets raw run lengths.
3. Attack multicolour branching overlaps with a genuinely unambiguous
   decomposition; a canonical witness alone does not count words.

# Independent review of PROOF.md (all-five cancellation, PROVED-PAPER)

Reviewer: Claude, branch research/free-cumulants-20261029, from-scratch code
(no reuse of GPT's `structure.py`, `pair_orbits.py`, `eliminate.py`, or
Claude's own prior `five_kernel.py`/`five_pairs.cpp`). Requested by GPT's
handoff note: "Please try to refute it before using it as an enumeration
premise."

## What was checked

1. **Geometric input to Section 3** (`verify_geometric_0_1_all.py`): is the
   pairwise local-choice compatibility relation between any two five-classes
   on a shared cycle always 0/1/All (universal, empty, forced-row, forced-col,
   two-fan, or matching of size <=2)? Checked exhaustively over ALL 252 raw
   interleavings of two labeled 5-point classes on a 10-cycle (not just the
   126/13-orbit representative set GPT used), with an independently written
   crossing test (full 4-way block crossing: pair-pair, pair-triple,
   triple-pair, triple-triple). Result: **0 violations**. Shape counts:
   empty 102, matching(size=1) 70, forced-row 20, forced-col 20, two-fan 20,
   universal 10, matching(size=2) 10 (sums to 252). CONFIRMED.

2. **Abstract collapse theorem, Section 4** (`verify_abstract_collapse.py`):
   for a finite binary CSP on k variables with a connected nonuniversal-
   constraint graph whose nonuniversal relations are each a two-fan or a
   size-2 matching, does |A|>=3 with no constant coordinate always give
   c(A)=0, and |A|=2 always give c(A)=-1? Generated 2500 random instances
   (k=2..8, domain size 2..5, random spanning tree + random extra edges,
   each nonuniversal edge a random two-fan or matching-2), computed the
   actual solution set A by brute-force CSP solving and c(A) via the
   (separately verified) projection formula. 438 cases had |A|>=3 with no
   constant coordinate; 292 had |A|=2. **0 failures either way.** Pushed
   past GPT's own stress tests (which went up to 5-6 variables, domain 5)
   to k up to 8 variables, |A| up to 65. CONFIRMED on this sample.

## What was NOT checked

- No attempt to re-derive or break the written proof of Section 4 itself
  (the majority-closure / bijective-elimination / maximal-fiber argument).
  Reading it closely, the structure is sound and the degenerate
  counterexamples GPT gives at the end (disconnected graph -> 4-cycle,
  alternating sum 1; bijection on 3 values -> violates matching-size-2 ->
  alternating sum -2) correctly show why the hypotheses are load-bearing.
- No independent re-verification of the Lean-compiling lemmas
  (`ChoiceComplexCancellation.lean` etc.) beyond trusting the reported CI
  (run 40952508624, success, standard axioms only) — I did not rebuild
  that commit on my own branch this session.
- Random generation is still sampling, not exhaustive, and cannot rule out
  a rare structural counterexample the construction can't reach (e.g. one
  requiring a specific non-tree topology my generator under-samples).

## Verdict

Both checks **survive independent, from-scratch adversarial testing** with
zero counterexamples. This raises my confidence that the central
>=3-certificate cancellation conjecture is genuinely true, and that GPT's
written argument (not just its sampling) is the reason. It remains
PROVED-PAPER, not PROVED-LEAN — the full theorem (quotient construction,
connectedness preservation, bridge to `winningJoinCoefficient`) is not yet
assembled in Lean, per GPT's own `REPORT.md`/`PROOF.md`. I did not find a
counterexample and am not withholding one.

## Status
Section 3 geometric input: **confirmed independently**.
Section 4 abstract theorem: **confirmed independently on 2500 random trials**.
Full all-five cancellation theorem: still PROVED-PAPER pending Lean assembly.

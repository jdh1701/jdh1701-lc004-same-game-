# Revised joint handoff — 29 October 2026

Read WORKBOARD.md, especially its latest GPT reconciliation, before starting.
Work on a new branch off research/free-cumulants-20261029; preserve main.
Objective: exact fixed-alphabet winning-word enumeration, especially A035617.

## Evidence rules

Use PROVED-LEAN, PROVED-PAPER, VERIFIED-COMP, CONJECTURE, KILLED or RETRACTED.
A status and its evidence are separate fields. For Lean require the exact SHA,
statement, import closure, successful build, axiom audit and green hosted run.
For paper proofs cite the argument and unresolved hypotheses. For computations
cite code/input hashes, arithmetic, range, run or local receipt, and method.
A CI run is not evidence for literature priority or an unchecked paper argument.
Retain negative results. Empty/blocked searches do not establish novelty.

## Revised execution order

1. Bounded provenance and novelty gate. Check the exact triangle and diagonals
   against OEIS, original Kurz/Burns–Purcell/Biedl sources, OpenAlex metadata and
   forward citations. Archive raw responses, query/date/status, candidate
   matches and reasons for exclusion. Cap the initial pass at one focused
   session; unresolved novelty does not block proof development. OpenAlex is
   a literature index, not a numeric-sequence search engine. Freeze the precise
   target definitions and distinguish known recognition from counting novelty.

2. Finish the crossed-four-class coefficient cancellation in Lean. Reuse PR #32
   (a2212dc08ca633cb6925208a865493648c237b0a): it adds 31 locally verified theorems,
   including the exact four-gap split-winning-indicator identity and collected
   coefficient uniqueness. Hosted run 40890080150 was in progress when reviewed.
   Do not reimplement the completed geometry or merge conflicting copies blindly.
   Use local incidence support below the target partition. The missing step is
   extending the overlap calculation to every refinement below that target,
   including refinements splitting the distinguished four-class, and showing
   invariance under meet with the four-gap partition. Prove the resulting
   coefficient vanishing before promoting the cumulant support bound.
   Gate: no assumptions encoding the desired cancellation; standard axioms only.

3. Independently discriminate the j=6 diagonal claim. Recompute A(16,5)=2306780
   and A(18,6)=23078316 without importing either value or bf_k.c. A face-profile
   calculation is an independent computational route but depends on that
   enumerative formula; mark that dependence explicitly. Prefer bounded-deficit
   coefficient extraction, pruning impossible contents and exact arithmetic.
   Cross-check all available lower lengths/profiles and control entries.
   Compare against a polynomial fitted on held-out-independent smaller k.
   Distinguish failure of an exact polynomial from failure of an asymptotic.

4. Adversarial review throughout steps 2–3. R1/R2 are precise existing Lean
   statements: inspect assumptions, original-game bridge, build closure and
   exact-run audit before spending more computation trying to refute them.
   Attack generalizations and cancellation assembly. Record contradictions
   without conflating geometric join existence with nonzero signed support.
   Existing independent signed-support checks extend through n=15, primary
   checkpoint 31a286a. Extend only for a specific discriminating question.
   Before fitting 65,286,117,..., quotient by cyclic rotation/reflection and
   separate rigid insertions from connected heavy kernels. Keep certificate,
   pattern, word, history and orbit counts distinct.

5. Integration after evidence gates. Inspect current PR ancestry and changed
   files, build a temporary integration branch, resolve duplicates, then build
   the full root and audit all declarations on the candidate merge commit.
   #26 -> #27 -> integration -> #28 is historical guidance, not a blind merge
   command: #28 currently targets integration, #31 targets the face branch, and
   #32 targets publication. Keep a documentation-only workboard PR separate.
   Pages configuration is optional publication work and must not block solving.
   No main merges or Pages setting changes are part of this handoff revision.

## Corrected claim boundaries

- The exact degree-(j-1) polynomial diagonal law and the involution asymptotic
  are different claims. Rational R6/R7 with genuine poles refute the polynomial
  extrapolation conditional on the face-profile expression; they can still
  have the predicted leading asymptotic. The asymptotic is not KILLED by that.
- Crossed size-four joins exist. The target concerns their collected signed
  coefficient being zero. The four-gap paper proof is preserved at primary
  commit 31a286a; complete Lean assembly remains open.
- Novelty remains unestablished. Full b>=3 enumeration remains unresolved.

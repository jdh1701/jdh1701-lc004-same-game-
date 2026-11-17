# Continuation index and archive completeness

Latest verified Lean source: proof repository commit a2212dc08ca633cb6925208a865493648c237b0a, PR #32.
Hosted CI run 40890080150: completed SUCCESS; exact head a2212dc.
https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40890080150
31 new theorems; 171 active modules; local audit 2,124 project declarations, standard axioms only.

Read research/FOUR_GAP_LEAN_CHECKPOINT_20261029.md at that commit for statements,
reproduction commands, environment limitations and unfinished obligations.
The nine new Lean modules are imported by LC004.lean there.

Primary repository computational/paper checkpoint: 31a286a1616a4a0bc8313d62190589545e361ffe.
Primary repository Lean mirror: 417efbafd64b55e3bd24d9014e8ad5c0a356e05c.
Both are on research/lc004-exact-audit-20261029 in jdh1701/Alexandria_Omega_New.

This branch contains the updated HANDOFF_TO_GPT_20261029.md, WORKBOARD.md,
cyclic-orbit script, exact result and input provenance, plus all currently
retained local four-gap build/failure/cache/audit/guard logs and their hashes.
The manifest explicitly records its scope. Failed source snapshots were not
saved independently, so the archive does not reconstruct every intermediate
source edit. Older failed CI runs remain in Actions; their historical links
and counterexamples remain in the workboard and earlier audit reports.

## Failures and corrections

- Initial executable lookup and Lake configuration failures: used the documented
  path-resolution shim and absolute executable paths; no kernel alteration.
- ProofWidgets release fetch failure: restored release successfully before cache.
- Incidence induction/conditional-sum elaboration failures: explicit well-founded
  relation and finite-sum proof; subsequent full build/audit passed.
- Local pair reflexivity/cardinality elaboration failures: explicit setoid
  reflexivity and matching local cardinality expressions; accepted final proofs.
- Wrong restrictColorPattern_mono argument order: corrected against its declaration.
- Collected-coefficient decidability/simplification failures: scoped Classical
  and direct list reduction; accepted final proof.
- Split-indicator decidable-instance mismatch: proved Boolean equality by cases.
- Negative guard harness initially could not locate Lean: absolute executable
  wrapper; both negative checks then passed.
- Cone-generator route is insufficient: 30 length-12 cases remain after component
  factorization, while coefficients vanish. Data are at primary checkpoint 31a286a.

## Exact next proof target

Extend four_gap_winning_indicator to all refinements below the target partition,
including refinements splitting its four-class. Apply local meet-invariance
support to the collected coefficient. The crossed-four coefficient cancellation
and cumulant support bound still lack complete Lean assembly. Full fixed-b
winning-word enumeration and scientific novelty remain unresolved.

Do not merge the research branches by file copying without resolving their
base differences and running the full root build/axiom audit.

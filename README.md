# One-dimensional Same Game

Lean 4 proofs and reproducible experiments on maximal-run deletion games.
The formal model records each run's colour and whether its length is at
least two. Complete solutions retain the sequence of current run indices.

The default build checks:

* unique successful first deletion iff unique complete successful path,
  for normalized nonempty run states;
* necessary median deletion, odd run count and palindromic colour skeleton;
* the entire unique index sequence `[m,m-1,...,0]` for `2m+1` runs;
* correctness of an exact finite successful-path enumerator;
* a concrete four-way ambiguity certificate: every proper subset of four
  optional heavy runs has one solution, but all four have 91 solutions.

The [current research report](research/checkpoint_2026_10_17/canonical/STATUS.md)
contains statements, assumptions, counts, failures, source provenance and
reproduction commands. The
[earlier checkpoint](research/checkpoint_2026_10_17/STATUS.md) records the
independent baseline reproduction and binary counting candidate.

```sh
lake exe cache get
lake build
lake env lean research/checkpoint_2026_10_17/canonical/PrintAxioms.lean
```

Lean is pinned to 4.19.0; dependencies are pinned in `lake-manifest.json`.
Python experiments use the standard library. Mathematical priority remains
under review. The full q>=3 winning-string enumeration and the unconditional
ordinary-cell/Boolean-state commuting theorem are not established here.

# Closure restriction checkpoint and method decision

PROVED-LEAN (local Lean 4.19.0; hosted CI pending): noncrossing closure
commutes with restriction to every block of any noncrossing coarsening.
Consequently every block of nc(p) contains an NCConnected restricted pattern.
Also proved general noncrossing assembly, restriction preservation, and local
characterization of noncrossingness. Five new theorems, no added assumptions.

This closes items 1 and the main structural lemma for item 2 in the preceding
REUSE_AND_NEXT.md. It does not yet construct the connected-fiber equivalence,
prove class-count additivity, or identify the weighted cumulant recurrence.
The complete enumeration remains unresolved.

Method decision: keep the structural Lean reduction, but prioritize an effective
enumeration of surviving connected weights as the discovery target. More verified
infrastructure alone does not establish that the main counting problem is close.
Use decisive counterexample tests rather than extending tables without a target.
The all-five Fuss-Catalan proposal is still CONJECTURE; its j=4 prediction needs
an independent check. No new literature or Sage computation was run here.

Claude handoff: reuse NoncrossingClosureRegions.lean; do not duplicate closure
restriction. Concentrate on connected-weight enumeration or a counterexample to
the all-five conjecture. The next formal task is the connected-fiber equivalence,
then quotient class-count additivity and the weighted cumulant bridge.

attempt01.log and attempt02.log preserve elaboration failures; attempt03.log
contains the successful full build. Failed intermediate source versions were
not separately saved. All final source and retained attempt logs are uploaded.

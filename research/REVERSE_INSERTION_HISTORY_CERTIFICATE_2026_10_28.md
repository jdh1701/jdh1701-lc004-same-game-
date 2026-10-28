# Reverse insertion history certificate — formally verified
Date: 2026-10-28
Merged PR: https://github.com/jdh1701/jdh1701-lc004-same-game-/pull/21
Merge: 7f984be1be22a2f80207b289c212547c03155016
Lean CI green: https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40744359507

## Precisely verified
- InsertionHistory w inductively inserts same-colored pairs or triples into arbitrary gaps, starting with the empty word.
- insertion_history_backwards: Erases u v and InsertionHistory v imply InsertionHistory u.
- erases_empty_to_insertion_history: Erases w [] -> InsertionHistory w.
- insertion_history_to_erases_empty: InsertionHistory w -> Erases w [].
- insertion_history_iff_erases_empty: Iff for every word.
- raw_max_win_to_insertion_history: A raw maximal-run winning history implies a reverse contextual insertion history, via previously verified maximal-run -> auxiliary erasure simulation.

## Kernel-provenance evidence
Build succeeded; #print axioms insertion_history_iff_erases_empty: 'does not depend on any axioms'.
#print axioms raw_max_win_to_insertion_history: [propext, Quot.sound].
The initial PR build failed due to dependent induction; the failing source reported sorryAx, so it was not merged. A generalized endpoint theorem fixed the proof and green CI removed sorryAx from the audited theorems.

## What this DOES NOT prove
The existence of an insertion history is not yet a *formal noncrossing partition certificate on the indices of the original word*. The next needed object is a partition of Fin w.length with monochromatic blocks of size 2 or 3 and a noncrossing predicate. The essential induction must transport old block indices through insertion gaps and add a new adjacent block, showing color-constancy, disjoint coverage, and noncrossing preservation. Then one can connect maximal-run winning histories to the combinatorial partitions used in the second-diagonal counting formula.

The reverse implication (auxiliary erasures -> raw maximal-run wins) is still not proven in the raw model. A CFG grammar equivalence theorem, full second-diagonal formula, and general n/q enumeration remain open.

## Suggested next formal proof sequence
1. Define insertion injection on Fin n using insert-gap arithmetic and prove order preservation.
2. Define partition certificates (blocks of sizes 2/3, color constancy, pairwise disjoint, cover all positions).
3. Show insertion preserves noncrossing blocks and adds one new innermost block.
4. Derive certificate from InsertionHistory by induction, formalizing forward history-to-noncrossing direction.
5. Prove converse by choosing an innermost block and removing it.
6. Relate certificate counting to second-diagonal formula using noncrossing partition enumeration and fourfold overlap corollary.

This is a non-tautological remaining mathematical bridge; the completed reverse-history equivalence is foundational but does not itself solve enumeration.

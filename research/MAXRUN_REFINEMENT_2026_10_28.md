# A rigorous unconditional half-bridge: maximal-run moves refine to pair/triple erasures
Date: 2026-10-28

## Theorem (mathematical argument, Lean formalization still pending)
For any finite word w and any legal maximal-run deletion w → w', there is a finite sequence of contextual adjacent pair/triple deletions w →* w'. Consequently every maximal-run-winnable word is erasable by adjacent pair/triple deletions.

## Proof
A selected maximal monochromatic run has length m >= 2, so w=x a^m y and w'=xy. Every integer m>=2 is a sum of 2s and 3s: for even m=2r use r pairs; for odd m=3+2r use a triple and r pairs. Sequentially delete the corresponding consecutive groups at the same position between x and y. All erasures are legal contextual pair/triple erasures, and the final word is xy. Concatenate the refinement sequences for every move in a successful maximal-run deletion path. QED.

The argument does not depend on the deleted run being maximal once one is simulating the deletion; each auxiliary step may delete a strict subrun.

## Executed independent Python regression
research/same_game_run_refinement_2026_10_28.py checked EVERY legal maximal-run deletion for:
- q=2, length <=12: 22,528 moves
- q=3, length <=10: 177,147 moves
- q=4, length <=8: 114,688 moves
Total 314,363 legal maximal-run moves, all refined correctly. This is a test, not the basis of the proof.

## What has NOT been established
The reverse implication (auxiliary erasability -> original maximal-run winnability) remains unproved. This is equivalent to handling the locally inserted pair/triple when it merges with neighboring runs; finite tests cannot replace proof.

The full grammar equivalence also requires the converse that every erasable word has a grammar derivation. The grammar is an existential noncrossing decomposition; reconstructing this from arbitrary erasures requires an independent argument.

## Lean status
Existing file LC004/GrammarErase.lean proposes formalization of the auxiliary erasure relation and grammar -> auxiliary erasure. This theorem about maximal run move simulation is not yet formalized in Lean and not kernel-certified. There is no available local lean or lake compiler and no accessible successful GitHub Actions build log for newly added modules. Do not count as a new Lean certificate.

## Distinct word enumeration
Still open; even a complete language characterization does not automatically yield an efficient unambiguous counting recurrence.

# Grammar → contextual erasure soundness (28 Oct 2026)

## Submitted theorem (NOT yet Lean certified)
File: LC004/GrammarErase.lean. Root import: LC004.lean. Latest root commit: 3762d6606f06c953bb9f163d660966eab8ad9d96.

A step erases two or three adjacent identical cells in arbitrary left and right contexts; Erases is its reflexive transitive closure. The file proposes:
- erases_trans
- smallErase_context
- erases_context
- erase_pair_composition and erase_triple_composition
- grammar_erases_empty: Grammar q w → Erases w []

Mathematical induction: For a pair constructor a u a v, erase u inside the context, then delete adjacent aa, then erase v. For triple a u a v a w, erase u, erase v, delete aaa, then erase w.

## Independent test
Executed /mnt/data/same_game_cycle3.py against all 3-color words of lengths 2 through 11. Three independently defined predicates (maximal run game, contextual adjacent pair/triple reduction, and grammar derivation existence) agreed with zero disagreement. This does NOT replace a general proof.

## Critical proof gap
The formalized result, even if compiled, concerns contextual pair/triple erasures. It does not establish correspondence to the ORIGINAL maximal-run game, nor the reverse characterization (winnable → Grammar), nor efficient distinct-word enumeration.

## Verification limitations
No local lean/lake executable; network DNS inaccessible; GitHub combined status and PR-scoped workflow-run endpoints returned no successful CI status. GitHub source writes succeeded but cannot be counted as kernel checking. No new Lean-verified result claimed.

# Noncrossing block-family insertion: Lean-verified checkpoint
Date: 2026-10-28
Repository: jdh1701/jdh1701-lc004-same-game-
PR #25: https://github.com/jdh1701/jdh1701-lc004-same-game-/pull/25
Final green run: https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40749454856
Merge commit: f5baf0107b5f5237210fc493108667a3e370aae4

## Certified theorems
File LC004/NoncrossingBlockFamily.lean:
- pairCross_symmetric: symmetry of crossing for two indexed pairs
- blocksCross_symmetric: symmetry for arbitrary lists of old positions
- blocksCross_shift_iff: insertion index shift preserves arbitrary old-block crossing
- noncrossing_block_family_shift: shifting all old blocks preserves pairwise noncrossing
- noncrossing_block_family_insert: adjoining a new contiguous block of size k<=3 to any old noncrossing family yields a new noncrossing family after shifting old indices

The imported LC004 root built successfully with full regression suite in CI. No sorry or new axioms were introduced in this module.

## Critical adversarial correction
First CI build failed on the claimed arbitrary-size insertion theorem. The proposed NoncrossingBlockFamily predicate quantifies over ALL pairs of blocks including a block with itself. Under BlocksCross, a block of FOUR or more distinct indices may cross itself, because two different pairs of indices from the same block may alternate. Therefore arbitrary-size insertion was FALSE in this formal representation. Restricting the fresh block to k<=3 and providing the finite bounds to omega resolved the issue. This is a genuine correction of theorem scope, not merely a tactic repair.

## Scope and open mathematical obligations
This module proves noncrossing only. It does NOT certify that blocks partition all original positions, are pairwise disjoint, are monochromatic, or carry Fin length bounds.

Next:
1. Define typed block certificates with positions in Fin n, covering exactly once.
2. Prove index-shifting preserves block cover/disjointness and color labels, with newly inserted 2/3 block.
3. Derive certificate from arbitrary InsertionHistory by induction.
4. Prove converse from noncrossing certificate to auxiliary erasure by innermost-block deletion.
5. Complete raw-maximal-run/grammar equivalence and any proposed second diagonal counting theorem.

No full q>=3 Same Game enumeration solution, bibliographic novelty, or numerical progress percentage is implied by the verified lemma.

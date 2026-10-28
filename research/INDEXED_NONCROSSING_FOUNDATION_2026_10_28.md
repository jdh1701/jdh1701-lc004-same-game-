# Same Game: indexed noncrossing insertion foundations — verified 2026-10-28

## Verified CI and merges
PR #22, merge b931c54d0b8ab5ab8ff5554ab62aeff995ce55d2: LC004/NoncrossingInsertionIndex.lean. CI workflow run 40745159614 passed.
PR #23, merge a4e833a64fa4942c761ed7674b7cce21471e1e94: LC004/PairFamilyInsertion.lean. CI workflow run 40746224862 passed, following one repaired failed compilation.

## Actual formal results
- shiftAfterInsertion_strict: shifting old indexed positions around an insertion gap preserves their strict order.
- shifted_old_outside_new_block: old positions never map into newly inserted positions.
- pairCross_shift_iff: crossing of two old pairs is invariant under the insertion index shift.
- old_pair_not_cross_new_pair: a pair of old positions does not cross any pair contained inside the newly inserted consecutive interval.
- pairFamily_noncrossing_shift: all old pair-family noncrossing relations survive insertion.
- pairFamily_noncrossing_insert_pair: adding a new adjacent pair to an ordered noncrossing old pair family yields another noncrossing pair family.

These are universally quantified Lean 4 proofs, but they use Nat pairs, not yet complete partition certificates on Fin n. They do not assert anything about color equality or block coverage in the original word.

## Error and correction
The first PR #23 build failed because dependent elimination on list membership attempted an impossible equation for mapped lists. Replacing destructuring-by-rfl with explicit equality rewrites fixed the formal proof; the final full Lean build succeeded, and only that corrected head was merged.

## Main remaining proof target
Create a certificate indexed by original word positions:
(1) blocks have sizes 2 or 3;
(2) positions are covered exactly once and blocks are disjoint;
(3) each block is monochromatic;
(4) blocks are pairwise noncrossing.

Then prove every reverse pair/triple InsertionHistory yields such a certificate, transporting all old indices by shiftAfterInsertion and inserting a fresh adjacent block. Existing PairFamilyInsertion addresses crossing only for size-two blocks, not triples, colors, coverage, and Fin-bounds. These must not be silently assumed.

The next theorem should cover arbitrary 2/3-block noncrossing insertion with a unified block crossing predicate; only then integrate complete certificates. The converse certificate -> deletability requires choosing an innermost block. Original-game/grammar equivalence and the second-diagonal formula remain outstanding, along with general 3+ color enumeration.

## Novelty and scope
Order-preserving insertion mappings and noncrossing preservation are classical structural ideas; the implementation is a project-specific formal foundation, not evidence of a novel solution. The full general Same Game counting problem remains unsolved.

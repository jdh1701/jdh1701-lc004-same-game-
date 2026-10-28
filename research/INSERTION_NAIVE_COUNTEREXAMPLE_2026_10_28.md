# Insertion closure: adversarial proof-strategy counterexample (2026-10-28)

## Reproduction
Executed research/same_game_insertion_cycle.py locally. It printed:
2 12 5187 503688
3 10 11800 1485480
4 8 4313 593296

These total 2,582,464 insertion checks, zero failures.

## Minimal obstruction to naive immediate deletion
Original word 0110 is winnable: delete 11 -> 00 -> empty.
Insert 00 at the beginning, yielding 000110. This word is winnable: delete 11 -> 0000 -> empty.
However deleting the maximal run 000 immediately yields 110, which is losing (11 -> 0).
Therefore the assertion "insertion is safe because one can delete the enlarged inserted run immediately" is false.

An exhaustive increasing-length search for q=2,3 found this counterexample first, at original length 4. This does not refute insertion closure itself.

## Consequences
The proof of insertion closure must allow a reordering of moves, or appeal to the existing Heavier/monotonicity simulation, rather than require the inserted block's maximal run to be deleted first.

The strongest immediate next lemma is a commutation lemma for deletions whose affected run is disjoint from the insertion site, followed by a critical-pair analysis when a deletion touches the insertion boundary. Beware that adjacency of runs changes after deletions.

## Verification
Python executed. No new Lean theorem was run. The existing proposed grammar Lean modules remain unverified by a compiler log. No solution to q>=3 enumeration is claimed.

# Original-game connected-weight expansion

PROVED-LEAN (local Lean 4.19.0): weighted_connected_fiber_product,
weighted_closurePushforward_product and weighted_game_noncrossing_expansion.
PROVED-LEAN: labeledWinningCount_collected and
labeledWinningCount_connected_expansion identify the noncrossing expansion
with the original maximal-run deletion game's labeled winning count.
The statements hold for all natural alphabet sizes and lengths, including zero.

Seven new theorem declarations were added across WeightedConnectedFibers and
LabeledConnectedExpansion. LabeledJoinEnumeration was reused from primary
commit d49ac53d77b49dd12e01166663ed5f7b9c0ab6ed at
research/LC004/2026-10-29-exact-audit/formal/LC004/LabeledJoinEnumeration.lean,
and rebuilt here; its existing theorems are not new research claims.
All newly printed theorem dependencies are standard axioms only.
Both initial module-build attempts passed; there were no failed Lean attempts
in this checkpoint. Full build/audit/guard receipts are archived separately.

This is the noncrossing moment expansion for the game itself. A separate
triangular recurrence uniqueness theorem and identification with any preexisting
cumulant definition have not yet been formalized. The connected weights are
still defined by finite signed sums, not an efficient new enumeration.

Next: formalize triangular uniqueness for n>=1, preserve the empty convention,
then combine coefficient support, R1/R2 and crossed-four cancellation to prove
the n<5j cumulant support bound. The discovery frontier remains effective
connected-weight enumeration; the all-five conjecture remains unproved.

Claude handoff: do not redo closure, fiber, class-count or labeled expansion
bridges. Reuse these files. Concentrate on connected-weight enumeration or
counterexamples to the all-five conjecture. No direct Claude call or new
literature/Sage run occurred in this checkpoint.

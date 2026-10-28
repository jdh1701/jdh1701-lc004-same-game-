# Same Game: arbitrary-block insertion conjecture — 2026-10-28

## Statement (unproved)
Let Win(w) mean w can be reduced to empty by deleting entire maximal monochromatic runs of size >= 2. For any words x,y, color a, and integer k >= 2:

  Win(x ++ y) -> Win(x ++ replicate k a ++ y).

This generalizes the contextual pair/triple lifting conjecture. It is NOT a theorem yet.

## New exhaustive experiment (actually executed in local Python)
For every winning word of lengths 0..N over q colors, insert each color at each of the n+1 gaps in blocks of lengths 2,3,4,5 and test maximal-run solvability of the result.

q=2, N=12: 5,187 original winning words; 503,688 insertions checked; zero failures.
q=3, N=10: 11,800 original winning words; 1,485,480 insertions checked; zero failures.
q=4, N=8: 4,313 original winning words; 593,296 insertions checked; zero failures.
TOTAL: 2,582,464 insertions, zero failures.

Note that the inserted result can have length N+5; these are NOT claims of exhaustive enumeration of all words up to that larger length. The experiment tests exactly the specified insertions of winning originals.

## Proof strategy
Try induction on a successful maximal-run deletion path for x++y. Analyze whether a deleted run intersects the insertion gap; if not, commute the move with insertion. If it does, use the existing heavy-run monotonicity and boundary-sensitive simulation to justify a replacement move. Naive deletion of the inserted block is invalid when it merges with surrounding cells of the same color.

## Significance
If this insertion theorem is proved, every auxiliary SmallErase u v with Win(v) yields Win(u), because u inserts a block of size 2 or 3 into v. Together with the conditional theorem grammar_implies_win_of_one_step_lift, this proves Grammar q w -> Win(w) for the actual maximal-run game.

## Verification
Only Python tests executed. No local Lean/lake executable found. GitHub commits do not establish Lean kernel verification. No general enumeration formula or bibliographic novelty claim is made.

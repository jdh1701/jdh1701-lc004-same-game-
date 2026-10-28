# Same Game: complete three-case insertion-closure proof architecture (2026-10-28)

## Mathematical result

Let W be the language of words clearable by deleting entire maximal monochromatic runs of length >= 2. Then for any words x,y, any color a, and any k>=2,

  W(xy) => W(x a^k y).

Proof by examining the insertion gap in xy:

Case 1. An adjacent cell has color a. Insertion lengthens the existing maximal a-run without changing the color-run skeleton. A run that was singleton becomes heavy, or an already heavy run remains heavy. Solvability is monotone under this run-heaviness increase, by the existing mathematical simulation theorem formalized as LC004.sameGame_solvable_mono_full. Thus the inserted word wins.

Case 2. Neither adjacent cell has color a, and the two sides of the insertion gap are in different runs of different colors (or a boundary is empty). The new a^k run is heavy and can be legally deleted immediately without merging the neighbors, returning xy. Thus the inserted word wins.

Case 3. Neither adjacent cell has color a, but the insertion gap cuts a single run of a different color b. The inserted a^k separates two nonempty b-run pieces. Its maximal-run deletion immediately merges those b pieces, recreating the original b-run, which is necessarily heavy. Thus the inserted word wins.

These cases exhaust all possible insertion gaps.

This is a mathematical proof of monochromatic-block insertion closure, conditional only on the established heaviness-monotonicity theorem; it is NOT yet a fully Lean-certified RAW-word theorem. The three cases have individually submitted Lean source in LC004/InsertionRunCases.lean:
- insertion_existing_run_solvable
- insertion_fresh_run_solvable
- insertion_bridge_run_solvable

The missing Lean integration is the raw-word run-encoding classification lemma showing each raw insertion falls into one of those run-state shapes. Source compilation status for these new files is unverified.

## Exhaustive checks executed in the local container

The independent maximal-run winning-path solver verified all insertion placements, all colors, and insertion lengths 2,3,4:
- q=2, all winning original words of lengths 0..10: 67,794 cases (46,050 adjacency/heaviness, 21,744 nonadjacency).
- q=3, lengths 0..8: 101,853 cases (46,422 adjacency/heaviness, 55,431 nonadjacency).
- q=4, lengths 0..6: 29,148 cases (9,660 adjacency/heaviness, 19,488 nonadjacency).
Total 198,795 checks with no failure.

NOTE: the prior two-case computer classification grouped both the fresh no-merge and inserted bridge-merge situations under 'nonadjacency'; the three-case mathematical proof above distinguishes them correctly.

## Consequences

The one-step lifting conjecture from LC004/ConditionalGrammarBridge.lean is now mathematically proved: if a pair or triple is erased from u to yield v, then u is obtained by inserting a block of length 2 or 3 into v, so Win(v) implies Win(u).

Combining the insertion theorem with the grammar-to-auxiliary-erasure soundness argument gives Grammar(q,w) => WinMaximal(w), mathematically, provided the auxiliary grammar-erasure induction in LC004/GrammarErase.lean is sound (it has a clear constructive proof).

The reverse implication WinMaximal(w) => Grammar(q,w) and an efficient distinct-word enumeration formula remain open.

## Verification and novelty limits

No Lean executable is available locally; GitHub's connected status queries have not returned CI success for the new files. GitHub commits are source submissions, not proof certificates. Existing run-level monotonicity was previously reported as certified but was not freshly kernel-checked this cycle. This statement is stronger than the finite tests but not yet an end-to-end formal proof. No bibliographic priority assertion is made.

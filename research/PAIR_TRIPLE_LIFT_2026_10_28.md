# Same Game: local deletion lifting conjecture and exhaustive falsification (2026-10-28)

## Core research proposition (NOT PROVED)

Let win(w) mean that the word w can be emptied by repeatedly deleting an entire maximal contiguous monochromatic run of length >=2. Suppose w = x + a^k + y with k=2 or 3 and let v=x+y. Claim:

    win(v) => win(w).

Here x and y can end/start with a, so the deleted cells may be a strict subrun of a longer maximal monochromatic run. In that case this is NOT an immediate legal Same Game step.

## Exhaustive falsification protocol
Independent recursive maximal-run win solver with memoization. For each q-color word up to a chosen length, check every contiguous repeated pair or triple, but only if original w is losing (so the implication's conclusion is false), and test whether the erased word v wins (the implication's hypothesis). A discovered example would immediately refute the conjecture.

Full results:
* q=2, lengths 2..12: 19,284 such potential counterexample tests, none found.
* q=3, lengths 2..12: 2,946,936 tests, none found.
* q=4, lengths 2..9: 746,880 tests, none found.
* Total: 3,713,100 candidate falsification tests, no counterexample.

IMPORTANT: the counts refer to tests of contiguous repeated pairs/triples on *losing originals*, not to the number of all input words, and multiple candidate deletions can occur per word. Finite agreement does not prove the universal proposition. Exact script: research/same_game_bridge_test_2026_10_28.py.

## Why this is the key bridge
If the implication is proved universally, any auxiliary reduction sequence of adjacent pairs and triples terminating at [] can be lifted backwards, one step at a time, to a maximal-run winning result. This would establish:

    Erases w [] => WinMaximalRuns w.

The current LC004/GrammarErase.lean supplies a *proposed, not yet kernel-verified* proof that Grammar q w => Erases w []. Thus the lifting lemma would yield grammar soundness with respect to the actual game once the repository Lean build succeeds.

## Main technical hazard
Deleting a non-maximal pair/triple inside a long run is not itself a legal original-game move. Simply rewriting SmallErase as a game transition would be mathematically invalid. A proof must establish that the residual run can be handled without destroying solvability after the entire maximal run is removed. The existing repo contains Heavier and sameGame_solvable_mono_full; investigate whether these support a correct simulation argument. Do NOT identify them as sufficient without a proof.

## Lean status
GitHub source LC004/GrammarErase.lean was added and imported into LC004.lean. No local Lean executable or GitHub build log is available. Neither this conjecture nor the previous proposed Lean source is certified in the present session. Do not label these as verified.

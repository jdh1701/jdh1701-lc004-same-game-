# Heavy multiplicities do not make deletion choices safe

## Result and status

The attempt to turn the empty-skeleton case into a greedy, duplication-free counting problem fails even when every color remains heavy after deletion. This is a negative result about a proposed strategy, not a solution of unrestricted enumeration or an established novelty claim.

Lean 4.19.0 locally verifies a winning compressed source state, a legal step to a losing compressed state, their concrete raw encodings, and their color counts. All eleven new declarations pass a transitive axiom audit allowing only propext, Classical.choice, and Quot.sound. The new file is checked explicitly from research/; it is not inserted into the frozen 162-module proof snapshot or the publication ledger.

## Exact concrete witness

The winning word is AAABAABBAB. Delete the BB in positions [6,8), then the initial AAA, then the middle AAA, then BB. This erases the word.

The other legal move deletes the AA in positions [4,6). Its child is AAABBBAB, with four occurrences of A and four of B. Its only legal first deletions remove either AAA or BBB. The former leaves BBBAB, whose only deletion leaves AB. The latter leaves AAAAB, whose only deletion leaves B. Both branches lose.

The Lean executable run indices for the winning path are [3,0,1,0]; the losing move has run index 2. These indices count maximal runs, whereas the intervals above count raw positions. The theorem heavyGreedy_nonconfluence is stated for the existing RunSolvable and Step relations. Separate encoding equalities connect the concrete words to those run states; the report does not silently promote this to a new theorem about RawMaxErases.

## Infinite family: ordinary mathematical proof

For r,s,t at least two, set w = A^r B A^s B^t A B. Removing B^t produces A^r B A^(s+1) B. Remove A^r, then the middle A run, then BB. Thus w wins.

Removing A^s instead produces v = A^r B^(t+1) A B. Its only deletable runs are its first A run and its B run. Removing the first leaves B^(t+1) A B, which reduces only to AB. Removing the B run leaves A^(r+1) B, which reduces only to B. Thus v loses.

After the bad move, A occurs r+1 times and B occurs t+2 times. For any prescribed threshold M, taking r at least max(2,M-1), t at least max(2,M-2), and s at least two gives a winning source and losing child whose appearing colors all meet M. Consequently no fixed global multiplicity threshold makes every threshold-preserving deletion safe. This parameterized family argument is not yet Lean-certified.

## Exact computations and independence

The Python experiment enumerates all 8,823 restricted-growth patterns through length 12 in which each appearing color occurs at least four times, including the empty word. A separate block-size recurrence verifies the number of generated inputs at every length. Breadth-first exploration retaining original color labels agrees with the existing memoized recursive maximal-run solver on every input. Certificate enumeration independently checks the two first counterexamples. The BFS and recursive methods share the intended maximal-run rule; their independence is algorithmic rather than an assertion of independent mathematical assumptions.

The first counterexample to deleting any run that leaves no singleton occurs at length 9: AABAABABB, deleting its initial AA. The first counterexample to deleting any run that leaves only heavy colors occurs at length 10: AAABAABBAB, deleting its middle AA. Minimality here means all shorter heavy restricted-growth patterns were examined, with canonical order within a fixed length. Minimality is computational, not part of the Lean theorem. The family was also tested on 196 parameter triples, independently of the unbounded mathematical argument.

## Failed attempts and reproducibility

An initial Lean attempt used decide directly on SuccessfulPath. The predicate did not synthesize a Decidable instance, and Lean rejected the file; its temporary sorryAx output was evidence of that failed elaboration, not an admitted proof. Replacing that step with definitional reduction (rfl) produced the passing proof. No sorry, admit, unsupported axiom, or native_decide is used in the delivered proof.

A finite Boolean search is used for the losing state. Its completeness for RunSolvable is proved by induction on fuel, using strict decrease in run count and completeness of executable indexed moves. Hence the computation false supplies a kernel-checked contradiction to solvability, not an external decision oracle.

Replay from the repository root:

    lake build LC004.ExecutableUniqueness LC004.RawEncoding
    lake env lean research/HeavyGreedyObstruction.lean
    python3 research/heavy_greedy_obstruction.py

The local runtime used the existing executable-path compatibility shim. Hosted CI uses the pinned normal toolchain. The proof and publication branches remain unchanged.

## Revised next experiments

1. Test candidate canonical rules against both witnesses before expensive counting. Color counts alone cannot certify a successful choice, even at arbitrarily large thresholds.
2. Compare exact residual-language states on equal run-count and multiplicity summaries; retain explicit distinguishing suffixes when such summaries collide.
3. Search for a finite or parameterized representation of those residual distinctions that supports counting without consulting the original winning-word predicate.
4. Keep the slot/profile formalization task active, while recognizing that it does not remove the empty-skeleton obstruction.

No literature priority claim is made for game nonconfluence or for this family. Its value here is eliminating two explicitly tested shortcuts and supplying permanent counterexamples to future recurrence proposals.

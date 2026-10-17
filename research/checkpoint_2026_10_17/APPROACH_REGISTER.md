# Exploration register — 17 October 2026

Baseline: `a9cb335c11b795372b7a4d22b68c6c4fab83239c`.
These are competing approaches, not results or priority claims.

| Approach | Mechanism and potential deliverable | Weakest assumption / smallest falsifier | Duplicate-counting issue |
|---|---|---|---|
| 1. Concentric unique paths | Prove every unique path deletes the median run at every stage; derive a necessary palindromic skeleton | Exchange lemmas must force the merged child run; test all short normalized states | Counting concentric witnesses alone may include branching states |
| 2. Independent shell flags | On a palindrome, require at most one heavy run in every mirror pair | Test seven runs with repeated shell colours | Different heavy shells can cooperate to create an alternate path |
| 3. Distinct shell colours | Restrict the concentric family so each shell has a different colour; obtain a weighted formula for a subclass | Exhaust short examples; prove deleting an off-centre heavy run strands its unique mirror | Check no two parameter choices encode the same raw word |
| 4. Minimal branching flag sets | For a fixed colour skeleton, exploit monotonicity to represent unique states by forbidden heavy subsets | Test whether minimal bad subsets stay bounded in size | Hyperedge overlap requires inclusion–exclusion or a decision diagram |
| 5. Last-deletion trees | Use the last deleted colour as root and the intervening deleted intervals as children | Find a short word with two root decompositions | Many deletion trees can represent one word |
| 6. Earliest solvable prefix | Split at the smallest nonempty solvable prefix | Test whether the suffix is always solvable | Boundary merges can invalidate independence |
| 7. Colour orbit enumeration | Enumerate restricted-growth strings, weight k-colour orbits by (q)_k | Cross-check labelled enumeration for q=2,3,4 | Do not quotient reversal; this is not a new general polynomial theorem (Kurz 2001) |
| 8. Weighted run states | Weight light runs by z and heavy runs by z²/(1−z) | Compare raw-word coefficients to independently enumerated counts | The Boolean quotient forgets the number of expansions |
| 9. Successful-first inclusion–exclusion | Count unions of events that a specified first move succeeds | Two legal first moves with the same successor must still be distinct choices | Intersections may need the entire state |
| 10. Residual language signatures | Identify prefixes by their effect on all suffixes | Increase suffix test length and search for splits | A finite experimental table does not prove fixed finite-state recognition |
| 11. Context-free recognition | Implement the published Clickomania grammar as an independent solver | Cross-check maximal-run deletion semantics on short strings | Grammar derivations are ambiguous and cannot be counted as words |
| 12. Bounded-colour multiplicity | Study words in which each colour occurs exactly twice; compare noncrossing pairings | Test crossing versus noncrossing pair partitions | Leading polynomial coefficients may already be classical Catalan numbers |
| 13. Recurrence discovery with holdout | Fit candidate recurrences on an initial coefficient segment and test later coefficients | First held-out mismatch | Finite fitting is never a proof |
| 14. Rewriting exchange classes | Quotient successful paths by local exchanges; seek a canonical representative | Test connectivity and compatibility with boundary merges | A canonical path does not itself give a tractable grammar |

Initial falsification: approach 2 already fails at seven runs. A concrete witness
will be saved with the executed experiment, including its alternate successful paths.
Promising scope: prove approach 1 against the existing Lean definitions, then use
approaches 3, 7, 8 and 11 for independent counting checks.

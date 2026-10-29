# Certificate constraints and ambiguity

Exploratory extension after the verified second-diagonal theorem. Novelty is not established.

A pair/triple noncrossing partition c imposes equalities on positions. A color pattern p admits that certificate precisely when c <= p in the partition lattice. Winning patterns therefore form a union of principal upper sets. Intersecting two upper sets replaces their generators by their lattice join, which can have crossing blocks.

Let C_n be the finite set of noncrossing partitions of n positions into pairs and triples. Inclusion-exclusion gives the proposed general counting identity

A(n,k) = sum over nonempty F subset C_n of (-1)^(|F|+1) S(blocks(join F),k),

where S is a Stirling number of the second kind. The empty-position certificate must be included at n=0. This is an exact finite enumeration construction, not a compact closed form or an efficiency claim. The complete identity is not yet proved in Lean.

Instead of enumerating all subsets F, keep signed coefficients indexed by their joins. On adding certificate c, retain the old coefficients, add +1 at c, and subtract each old coefficient at its join with c. Equal joins are collected. This is the grammar analogy's ambiguity correction expressed algebraically.

`certificate_join_count.py` implements this procedure and checks both the resulting counts and the pointwise winning indicator against independent maximal-run deletion for every set partition through length 9. All checks passed. At length 9, 96 certificate constraints compress to 232 nonzero signed join terms; the winning row is 1, 138, 300, 84.

`LC004/CertificateConstraintJoins.lean` provides the initial formal claims: winning is upward closed under color identification; joining constraints multiplies their indicators; and the signed inclusion-exclusion update preserves a union indicator. Consult CI for compilation status.

## Further formal development

Three additional modules implement the next bridges:

- `CertificateJoinIteration.lean` defines a recursively expanded list of signed joins and proves its score equals the indicator that at least one input constraint is satisfied. This theorem accepts arbitrary finite lists, including duplicates and the empty list. It retains duplicate join terms; coefficient compression is not yet formalized.
- `WinningConstraintGenerators.lean` defines the finite family of noncrossing pair/triple partitions. It proves that a color pattern is winning exactly when it coarsens one of these generators, then proves the unconditional signed-join winning indicator. The family includes the empty certificate at length zero.
- `PatternCoarseningCorrespondence.lean` applies mathlib's `Setoid.correspondence`, proves preservation of the number of resulting classes using the quotient isomorphism theorem, and restricts the equivalence to exactly k classes. This identifies the objects that the Stirling numbers must count; it does not yet identify their cardinality with a numerical Stirling recurrence.

The pointwise theorem is `winning_signed_join_indicator`. The quotient cardinality bridge is `patternCoarseningClass_card`. Compilation and the global axiom audit are enforced by the PR workflow; inspect the run for the exact commit being used.

The independent all-pattern check through length 9 is now a CI step, rather than a manual-only experiment.

Remaining formal obligations for the displayed Stirling-number formula: identify the cardinality of k-block partitions of a finite quotient with the standard Stirling number; sum the pointwise identity over patterns with k classes and interchange the finite sums; and, if using the compressed implementation, prove coefficient collection preserves the score. Higher-diagonal simplification requires structural information about which joins survive cancellation. These constructions establish no novelty claim and no polynomial-time bound.

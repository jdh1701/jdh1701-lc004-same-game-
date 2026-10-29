# Certificate constraints and ambiguity

Exploratory extension after the verified second-diagonal theorem. Novelty is not established.

A pair/triple noncrossing partition c imposes equalities on positions. A color pattern p admits that certificate precisely when c <= p in the partition lattice. Winning patterns therefore form a union of principal upper sets. Intersecting two upper sets replaces their generators by their lattice join, which can have crossing blocks.

Let C_n be the finite set of noncrossing partitions of n positions into pairs and triples. Inclusion-exclusion gives the proposed general counting identity

A(n,k) = sum over nonempty F subset C_n of (-1)^(|F|+1) S(blocks(join F),k),

where S is a Stirling number of the second kind. The empty-position certificate must be included at n=0. This is an exact finite enumeration construction, not a compact closed form or an efficiency claim. The complete identity is not yet proved in Lean.

Instead of enumerating all subsets F, keep signed coefficients indexed by their joins. On adding certificate c, retain the old coefficients, add +1 at c, and subtract each old coefficient at its join with c. Equal joins are collected. This is the grammar analogy's ambiguity correction expressed algebraically.

`certificate_join_count.py` implements this procedure and checks both the resulting counts and the pointwise winning indicator against independent maximal-run deletion for every set partition through length 9. All checks passed. At length 9, 96 certificate constraints compress to 232 nonzero signed join terms; the winning row is 1, 138, 300, 84.

`LC004/CertificateConstraintJoins.lean` provides the initial formal claims: winning is upward closed under color identification; joining constraints multiplies their indicators; and the signed inclusion-exclusion update preserves a union indicator. Consult CI for compilation status.

Remaining formal obligations: finite certificate partitions with an exact refinement characterization; induction over their enumeration and coefficient collection; a bijection between k-class coarsenings of a partition with b classes and k-block partitions of its quotient (cardinality S(b,k)); and the final finite-sum interchange. Higher-diagonal simplification then requires structural information about which joins survive cancellation.

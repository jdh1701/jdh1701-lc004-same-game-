# Component factorization: mathematical argument and Lean boundary

Let Π(X) be the finite lattice of equivalence relations on a finite linearly
ordered set X, ordered by refinement. Let V(X) consist of noncrossing partitions
whose blocks have size two or three. Define

`F_X(p) = 1` if some `v in V(X)` refines p, and `0` otherwise.

Let a_X be the collected signed coefficients of the union of all witness
events. The signed-union identity gives

`F_X(p) = sum_(r <= p) a_X(r)`.

This identity, with partitions rather than labelled words as the evaluation
domain, is `collected_union_zeta`. Lower-ideal sums determine a_X uniquely
(`zetaSum_injective`). These are formal Lean theorems, not new mathematical
inversion principles.

## Argument for noncrossing component factorization

Fix a noncrossing partition s of X, and a partition p refining s.

1. Restrict each partition r refining p to every block B of s. This gives an
   order isomorphism from the ideal `[bottom,p]` to the product of the ideals
   `[bottom,p restricted to B]`. The inverse takes the disjoint union of the
   component equivalence relations. It neither equates positions from distinct
   s-blocks nor loses any relation within a block.
2. A witness v refining r is a noncrossing pair/triple partition exactly when
   all its restrictions to the s-blocks are. Restriction preserves block sizes
   because v refines s. Conversely, assembling noncrossing partitions inside
   noncrossing s-blocks cannot produce a crossing between different s-blocks.
   Lean proves the precise equivalence as `pairTriple_iff_blocks`.
3. Existence of such witnesses therefore factors:
   `F_X(r) = product_B F_B(r restricted to B)` for every r refining p.
   The implication from component witnesses to a global witness uses the
   disjoint-union inverse from step 1; this construction is not encoded yet.
4. Under the product isomorphism, the product of the component coefficient
   functions has exactly these lower-ideal sums. Uniqueness gives

   `a_X(p) = product_B a_B(p restricted to B)`.

Taking s to be the noncrossing closure of p yields the previously tested
component formula H1. Standardization of each ordered subset B preserves
both crossings and block sizes, so only its relative order matters.

This is an ordinary mathematical proof argument for the partition-witness
model. It is independent of the unproved reverse raw-game/grammar bridge.
Its status is stronger than finite experimental support, but it is **not yet
an end-to-end Lean theorem about the existing generator or W(q,n)**.

## What the new Lean files certify

- `CoefficientFactorization.lean` proves uniqueness of cumulative coefficients,
  factorization on product posets, evaluation of collected signed terms, and
  coefficient factorization for actual Cartesian-product witness lists.
- `NoncrossingRestriction.lean` proves noncrossing restriction/reconstruction
  for a given refining partition, preserves fine-block cardinalities, and
  proves the full pair/triple property equivalence across coarse blocks.

The remaining formal assembly is the explicit order isomorphism in step 1,
construction from independently supplied block witnesses, finite-product
transport of coefficients, invariance under order-preserving standardization,
and equivalence with the executable witness generator (roadmap C2). Neither
new module assumes those obligations as axioms.

## Limits and next decisive obstacle

Factorization reduces the problem to connected coefficients; it does not
compute them. The minimum-five-position conjecture still needs a cancellation
proof, especially for four-position blocks. Even if true, its degree bound
allows new connected coefficients at later lengths. A recurrence that merely
renames unknown counts as connected weights does not solve enumeration.

Primary background read: Franz Lehner, *Free cumulants and enumeration of
connected partitions*, https://arxiv.org/pdf/math/0110030 . The paper develops
partition-lattice inversion and connected-partition interpretations of free
cumulants. It motivates this framework but does not itself establish the
Same Game witness specialization. No novelty conclusion follows from this
checkpoint; the inversion/product machinery is standard.

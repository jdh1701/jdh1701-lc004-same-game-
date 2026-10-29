# LC004 Face Decomposition: independent proof-obligation audit (2026-10-28)

Status: AUDIT / OPEN OBLIGATIONS. This file is not a Lean certificate, does not assert that the face theorem has been proved by Lean, and does not change any established theorem.

## Source baseline

Derived from proof/second-diagonal-counting-20261028 (branch head 72cb6a8270142a3c367fde1f9da7b78092bae7ba) and the user-supplied Face Decomposition Compendium. In LC004/CertificateConstraintJoins.lean, the following statements are written as theorems: winning_pattern_upward_closed, constraintIndicator_join, and constraint_join_union_update. The compiler/CI status of this audit branch has not been checked.

## Precise theorem target

For a winning colour pattern p with rigid classes of size 2 or 3 and heavy classes of size at least 4, fix the rigid skeleton R and partition the remaining positions into faces determined by its noncrossing blocks. Prove:
(1) each certificate contains every rigid class as an entire block;
(2) a certificate block containing heavy positions is contained in a single face;
(3) restrictions of a global certificate produce winning certificates within each face;
(4) certificates chosen separately for all faces, joined with rigid classes, yield one globally noncrossing complete certificate.

The face relation must be defined without ambiguity for empty rigid skeletons, for the cyclic cut, and for two endpoints on a boundary. An informal 'no rigid block has points on both arcs' is a candidate definition, not a Lean equivalence until proven.

## Adversarial proof gates

F-A. Exhaust the elementary crossing cases of two certificate blocks in distinct faces; give an explicit noncrossing-transitivity/arc-separation lemma rather than relying on the diagram argument.
F-B. Prove every mapping between face subwords and global positions is an order embedding, preserves colour equality, and preserves the predicate of a noncrossing partition.
F-C. Prove that rigid blocks and lifted face blocks are disjoint, have sizes 2/3, cover all positions exactly once, and are noncrossing pairwise.
S-A. For a face with p distinguishable slots and a word of length t, formally prove the weak-composition count binomial(t+p-1,p-1). Check the outer-face extra slot carefully.
S-B. Prove that the resulting slot/word encoding is injective as well as surjective, especially when different heavy classes have equal sizes.
G-A. State the exact rooted/unrooted convention of the Goulden-Jackson formula; prove the outer-face gap weighting and the derivative operator used in the generating-function summation.
G-B. Prove the displayed coefficient calculation including the w=0 and b=1 boundary cases separately, if necessary.
D-A. The 40-point diagonal comparison is not itself a proof. State a uniform upper bound on the numerator degree after clearing every denominator and ensure no evaluation point hits a pole; only then use root counting.
N-A. Novelty requires an independent literature and OEIS search; source absence is not mathematical proof of priority.

## Lean implementation order

1. Define rigidClass and heavyClass for a ColorPattern, and separate the noncrossing rigid skeleton.
2. Define a concrete face equivalence via separation by rigid classes (or a planar interval model).
3. Prove certificate blocks are confined to a unique face.
4. Prove noncrossing preservation under restricted/lifted blocks and disjoint face assembly.
5. Establish the iff face lemma, then independently certify profile counting and generating-function identities.

## Zero-overclaim policy

No result in this document is designated PROVED-LEAN. The correct next test is a compilation of the actual Lean module with the repository's pinned toolchain and a successful axiom-audited CI run on the exact head commit.

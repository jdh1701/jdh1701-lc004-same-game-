# Cancellation for the entire witness family

Date: 2026-10-18. Base commit: `041feb078cd1ade2f833fe076656b4cd759c2014`.

The previously conditional four-position result is now proved for **all
noncrossing pair/triple witnesses**, at every board length. There is no
assumed coverage, branch-completeness, or intersection-invariance premise.
The general winning-word enumeration problem remains unresolved.

This checkpoint adds **31 named Lean theorems, including helpers**, plus
two concrete examples. The nine-stage roadmap now has **4 verified,
2 partial, 3 open** stages. Stage F changes from open to partial because
there is now an unconditional structural coefficient law for the entire
specified witness family. Its completion requirements have not changed:
the remaining coefficients and growth analysis are still missing. No
additional major stage is declared complete. Five stages still need work.
The current snapshot is `STAGES.json`; the historical bridge snapshot is
preserved for its original audits.

## Main theorem

Let W_n be the finite family of all noncrossing partitions of n ordered
positions whose blocks have size two or three. For a partition P, define
a_n(P) to be its collected coefficient in the signed inclusion-exclusion
expansion of W_n, with intersections represented by joins in the lattice
of **all** partitions.

Choose four positions a < b < c < d. Let P consist of the block
{a,b,c,d} and an arbitrary partition p of the other positions. Divide
the other positions into the four cyclic gaps: (a,b), (b,c), (c,d), and
the exterior consisting of positions before a or after d.

**If p relates positions from different gaps, then a_n(P) = 0.**

Equivalently, if a_n(P) is nonzero, every block other than {a,b,c,d}
stays inside one cyclic gap. The formal declarations are
`all_witness_four_block_zero` and `all_witness_four_block_support` in
`LC004/AllWitnessCancellation.lean`.

This is a statement for arbitrary n, endpoint positions, and remainder
partitions, not a finite census. The theorem uses `allPairTripleWitnesses n`,
defined as the complete finite specification of valid setoids. It does not
use a supplied list assumed complete. The list is noncomputable and is not
yet identified in Lean with the executable Python generator.

## The missing argument is now closed

1. **Exhaustive classification.** A valid pair/triple partition on four
   ordered positions is exactly the adjacent pairing (a,b),(c,d) or the
   nested pairing (a,d),(b,c). The proof uses block cardinalities,
   equivalence-relation transitivity, and noncrossing.
2. **Restriction and extension.** Restricting a witness to either part
   preserves whole blocks and their cardinalities. Conversely, a regional
   witness and either selected pairing extend to a full-board witness.
   The appropriate chord barrier proves noncrossing across the two parts.
3. **Exact family identification.** `mem_fullBoardFourBlockFamily_iff`
   proves that membership in the constructed family is equivalent to
   being any valid full-board witness that keeps the selected positions
   separate from the remainder. Both directions are proved.
4. **Cancellation without a coverage assumption.** Locality restricts
   attention to witnesses below P. Exact family identification supplies
   the old `hcover` premise, and the earlier regional cancellation theorem
   then gives zero for the entire family.

| Module | Named theorems | Role |
|---|---:|---|
| `WitnessEmbedding.lean` | 12 | Saturated restriction, block sizes, full-board reconstruction, noncrossing and witness extension |
| `QuadWitnessClassification.lean` | 6 | Exhaustive four-position classification and validity of both pairings |
| `QuadWitnessGeometry.lean` | 5 | Ordered selected/complement embeddings and exact chord-barrier identities |
| `AllWitnessCancellation.lean` | 8 | Complete-family identification, cancellation and the support consequence |

## What this does and does not establish

The four-position cancellation conjecture is no longer merely finite
evidence or a conditional theorem about a chosen regional family. It is
kernel checked for the entire specified witness family. This is the
substantive structural advance in this checkpoint; the helper count is
not a count of novel mathematical discoveries.

Originality remains unestablished. See `NOVELTY_UPDATE.md`. A new proof in
this repository is not evidence that a result is absent from all prior
literature. The earlier numerical prior-art correction remains in force.

The complete minimum-five connected-support theorem is still open in Lean:
the size-two and size-three cases and the component-level conclusion need
assembly. Full factorization over noncrossing-closure components also needs
assembly. Even minimum-five support would restrict possible coefficients
without determining them all.

The remaining five major stages are B (grammar-to-raw direction), C2
(generator soundness/completeness), E2 (executable compression refinement),
F (complete useful structural/recurrence method with growth analysis), and
G (end-to-end enumeration theorem and originality assessment). B and F
are partial; C2, E2 and G are open.

## Verification

All four modules compile under pinned Lean 4.19.0. `PrintAxioms.lean`
prints the three key signatures and dependencies of all 31 named theorems.
Only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`,
or subsets, occur. `Nonvacuity.lean` proves that the crossing-gap premise
is inhabited by a twelve-position instance and specializes the theorem
to that instance. This checks premise satisfiability; it is not a new census.

The source audit scans LC004 and the new certificate files for proof holes,
custom axioms and unchecked native proof shortcuts. GitHub CI builds the
full root, runs every previous experiment and audit, and generates fresh
axiom and nonvacuity checks for this checkpoint. Local builds are targeted,
not full-root builds, because the aggregate Mathlib object is missing from
the local cache. All failed and successful development logs are retained.

```sh
lake build LC004.AllWitnessCancellation
lake env lean research/checkpoint_2026_10_18/coverage/PrintAxioms.lean
lake env lean research/checkpoint_2026_10_18/coverage/Nonvacuity.lean
python3 research/checkpoint_2026_10_18/coverage/audit.py
```

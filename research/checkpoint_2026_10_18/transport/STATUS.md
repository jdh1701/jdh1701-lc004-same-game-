# Subsequent progress (2026-10-18)

The [complete-family checkpoint](../coverage/STATUS.md) now proves exhaustive
classification, witness restriction/extension, and exact family identification.
It discharges the `hcover` premise for all pair/triple witnesses and proves
`all_witness_four_block_zero`. The body below preserves this earlier
checkpoint's boundary. Originality remains unestablished.

# Coefficient locality and full-board transport

Date: 2026-10-18. Base commit: `9f56ef71e9738fe9e86e6f8c7468ba2785f3b4b9`.

The general enumeration problem is **not solved**. This checkpoint adds
**23 named Lean theorems, including helpers**. The fixed roadmap remains
**9 major stages: 4 verified, 1 partial, 4 open**. Five stages need further
work; this is not a percentage estimate of distance to a solution.

## Novelty correction

The literature check found that OEIS A323844 already lists the polynomials
we computed at lengths 12–15, and also lists length 16. Our finite numerical
formulas are reproductions, not new formulas. Internal predictions still
record the order of our calculations, but do not establish public novelty
or a blinded test against all external knowledge. Existing logs and hashes
remain unchanged. See [NOVELTY_AUDIT.md](NOVELTY_AUDIT.md) for sources,
access limitations, and a precise distinction between prior work and the
candidate contribution. The script `check_prior_art.py` checks every
coefficient at lengths 12–15 against the transcribed OEIS data.

No mathematical originality is established. The specific signed small-block
cancellation law remains a candidate for further originality assessment.
The new generic locality and partition-product lemmas formalize standard
mathematics; they are useful proof infrastructure, not originality claims.

## What Lean now proves

| Module | Named theorems | Result |
|---|---:|---|
| `CoefficientLocality.lean` | 3 | Coverage below a target determines its coefficient; witnesses not refining the target may be discarded |
| `CoefficientTransport.lean` | 3 | Signed terms and coefficients commute with injective join-preserving maps |
| `SeparatedPartitions.lean` | 9 | Product of disjoint-part partition lattices, restriction/reconstruction, ambient join preservation, relabeling and coefficient transport |
| `FullBoardCancellation.lean` | 8 | Actual four-position/complement bijection and cancellation for the mapped regional family on `Fin n` |

`separatedPartitionOrderIso` explicitly constructs the product order
isomorphism onto partitions that keep the two carrier parts separate.
The joins are joins in **all equivalence relations**, not noncrossing joins.
`quadSplitEquiv` constructs the splitting for arbitrary a < b < c < d;
there is no assumed endpoint bijection.

For a remainder partition p that connects distinct cyclic gaps,
`fullBoard_four_block_zero` proves zero coefficient at the full-board
partition with selected block {a,b,c,d} and remainder p. The coefficient
belongs to the explicitly defined `fullBoardFourBlockFamily`: the image
of the complete regional adjacent/nested branch family. This theorem
has no coverage premise. Its family is nevertheless not yet proved equal
in coverage to the family of **all** valid pair/triple witnesses.

`fullBoard_four_block_zero_of_coverage` transfers zero to any supplied
full-board witness list with matching coverage below the target. That
theorem has an explicit `hcover` premise. We have not discharged it for
the entire witness family. The specification lists are noncomputable;
these results do not verify the executable Python generator.

## Immediate remaining obligations

1. Classify every valid witness refining an isolated four-position block
   as using the adjacent or nested pairing.
2. Prove both directions of witness restriction and extension across the
   selected positions and remainder, and discharge `hcover` for all witnesses.
3. Assemble the size-two, size-three, size-four and crossing-component
   results to obtain the proposed minimum-five support law. Full
   factorization over noncrossing-closure components also needs assembly.
4. Complete the existing grammar-to-raw direction and executable generator
   and coefficient-map refinement obligations (stages B, C2, E2).
5. Determine the remaining connected coefficients by a useful general law
   with growth analysis and prove the end-to-end W(q,n) theorem (F, G).

These are local research obligations, not a replacement for the fixed
nine-stage roadmap. The two locality/transport obligations from the
previous checkpoint are now discharged. Even a minimum-five theorem
would be a structural restriction, not a complete enumeration formula.
Since the finite polynomials are already published, the strategy now
prioritizes the universal cancellation/coverage argument over extending
the table. Length 16 is no longer available as an external holdout.

## Verification and reproduction

The pinned Lean 4.19.0 targeted build accepted all four new modules. The
literal report checks the axiom dependencies of all 23 named theorems.
The source audit rejects proof holes, custom axioms and unchecked native
proof shortcuts in LC004. Only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, or subsets, are accepted in the report.
Definitions that construct equivalences are also kernel checked in the
module build; they are not added to the named-theorem count.

```sh
lake build LC004.FullBoardCancellation
lake env lean research/checkpoint_2026_10_18/transport/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/transport/check_prior_art.py
python3 research/checkpoint_2026_10_18/transport/audit.py
```

The root imports the new modules. GitHub CI runs the full `lake build`,
all previous checks, and a freshly generated axiom report for this checkpoint.
The local build is targeted because the local cache lacks the aggregate
Mathlib object; it must not be reported as a local full-root build.
Successful and failed literal logs are described in `logs/README.md`.
This checkpoint performs no new word census and makes no new finite
enumeration claim.

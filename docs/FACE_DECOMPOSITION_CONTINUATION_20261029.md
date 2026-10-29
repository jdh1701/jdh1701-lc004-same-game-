# Structural Face Decomposition: continuation checkpoint

This continuation closes the reverse assembly and full structural winning-if-and-only-if obligations left open in the earlier heavy-face campaign. Historical ledgers remain snapshots of their stated commits.

## Exact mathematical result

`winning_iff_heavy_face_decomposition` proves, for every finite color pattern `p`, that it is winning exactly when (1) every color class has at least two positions, (2) the chords of its size-two and size-three classes have no alternating endpoints, and (3) the increasing subword of every complete heavy face is winning. A heavy position belongs to an original color class of size at least four. A face consists of all heavy positions with the same open-interval membership signature for every rigid chord.

`raw_win_iff_heavy_face_decomposition` states the same equivalence directly for maximal-run deletions of an arbitrary `Fin n -> Fin q` coloring, preserving the original colors in face subwords. The theorem covers `n = 0`, empty heavy faces, and an empty rigid skeleton. It assumes neither a global certificate nor path locality nor boundary saturation.

The reverse proof constructs an equivalence relation from local pair/triple certificate partitions on disjoint ordered regions. Quotient indices select each rigid color and geometric face once. Exact coverage comes from the no-singleton condition. A rigid chord excludes crossing heavy-face blocks; alternating pairs in two heavy faces force the same face. Thus the assembled relation has classes of size two or three, is noncrossing, and refines the original color pattern. The established certificate correspondence yields a win.

## Verification at this checkpoint

All three new modules compiled with pinned Lean 4.19.0. The main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The local runtime uses the previously documented executable-path compatibility shim; hosted verification is required separately and will be recorded with its exact source SHA.

The independent audit exhaustively checks 142,418 color patterns through length 10. For 22,083 patterns without singleton colors it filters all set partitions for noncrossing monochromatic pair/triple blocks, independently of the recursive certificate solver. It finds 2,592 winning patterns and 6,707 global certificate partitions. Every one of those 6,707 partitions is recovered uniquely by face assembly. All 7,300 noncrossing-skeleton cases satisfy the exact product identity, including zero products for losing faces. The later `heavyFaceCertificateEquiv` and `certificate_partition_count_product` now prove the corresponding partition equivalence and product identity in Lean for every finite length, under the no-singleton and noncrossing-skeleton conditions.

The three hypotheses are individually necessary: `A` refutes removing the no-singleton condition; `ABAB` refutes removing rigid-skeleton noncrossing; `ABABABAB` refutes removing face winning. Each word satisfies the other two conditions and loses.

## Claim boundaries and research queue

Completed: reverse assembly, full structural Face Lemma, its maximal-run formulation, a bijection of global certificate partitions with the product of distinct heavy-face certificate partitions, and the resulting cardinality product. Previously verified: geometric confinement, actual-certificate join restriction, and uniqueness from heavy face restrictions.

Still open at this checkpoint: ordered-slot/weak-composition correspondence; exact profile coefficient and automorphism accounting; unrestricted multi-color enumeration. Certificate partitions must not be counted as winning color patterns (for example `AAAA` has two certificate partitions).

This is a formalization milestone for the geometry already described in the repository, not a claim of new mathematical priority. No new sequence identification is asserted. The earlier primary-source novelty assessment remains applicable. When no rigid colors exist, the sole heavy face is the original word, so the equivalence does not itself solve unrestricted enumeration.

Alexandria Core remains frozen at `fb413043cb0f4369615132e014691782a344af8a`. The queued targets `gluing` and `face-iff` passed hosted run 40830582287 at `cf3f20ea1d40f5a7f11fb4046fa31f913d048d4c`. The additional `partition-equivalence` target is now locally compiled and axiom-audited, with hosted confirmation pending for its own source SHA. No duplicate research architecture or unmeasured performance improvement is introduced.

## Exact certificate product

Write `C(p)` for the finite type of pair/triple noncrossing equivalence relations refining `p`. This removes the irrelevant ordering of certificate lists. With no singleton colors and a noncrossing rigid skeleton,

`C(p) ≃ ∏ q : Quotient (rigidFacePattern p), C(p restricted to the complete heavy face of q)`.

Here the product notation denotes a dependent function type. `heavyFaceCertificateEquiv` proves both injectivity and surjectivity. Injectivity uses rigid-class forcing and actual-certificate geometric confinement. Surjectivity assembles the supplied local partitions exactly, not merely some witnesses of winning status. `certificate_partition_count_product` then applies finite cardinality to obtain the numerical product. Quotient classes that have no heavy positions contribute the unique empty partition and hence a factor of one.

The product can vanish when a face is losing. A global winning hypothesis is not assumed. For `AAAA`, the product is two although there is only one fixed winning color pattern; consequently this result alone is not a count of winning words.

## Reproduction

On the pinned Lean 4.19.0 toolchain with the repository Mathlib cache:

```sh
lake build
python scripts/check_lean_coverage.py
lake env lean scripts/FaceAxiomAudit.lean
python research/rigid_face_geometry_check.py
python research/heavy_face_assembly_check.py
```

Focused local compilation used `lake build LC004.HeavyFaceCertificateProduct`; hosted CI performs the full root build. The final local transitive audit checks 638 project declarations, and all 162 active modules are in the root import closure.

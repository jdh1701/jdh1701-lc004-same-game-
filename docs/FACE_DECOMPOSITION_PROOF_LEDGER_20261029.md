# Face Decomposition proof ledger

Exact final proof source: [`3446f6313f1f8a35a3c7891d5deece19c4599855`](https://github.com/jdh1701/jdh1701-lc004-same-game-/commit/3446f6313f1f8a35a3c7891d5deece19c4599855). [Hosted full build and audits](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40831342439) passed on pinned Lean 4.19.0. Draft [PR #28](https://github.com/jdh1701/jdh1701-lc004-same-game-/pull/28) retains the isolated branch and original integration base.

The mathematical milestones are the full structural winning iff, its original maximal-run formulation, the bijection of certificate partitions with their distinct-face restrictions, and the exact certificate cardinality product. Supporting declarations are listed for auditability, not as a measure of mathematical progress.

The transitive audit permits only `propext`, `Classical.choice`, and `Quot.sound` and checks 638 project declarations. The source guard rejects placeholders, native decision oracles, custom axioms, unsafe and partial source. All 162 active modules lie in the full root import closure. Local files match the hosted Git blob hashes.

| Declaration | Kind | Exact source | Verification |
|---|---|---|---|
| `LC004.assembledPattern` | def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/OrderedCertificateAssembly.lean#L7) | Local and hosted |
| `LC004.assembledPattern_local` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/OrderedCertificateAssembly.lean#L26) | Local and hosted |
| `LC004.assembledPattern_constraint` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/OrderedCertificateAssembly.lean#L46) | Local and hosted |
| `LC004.winning_of_ordered_region_cover` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/OrderedCertificateAssembly.lean#L84) | Local and hosted |
| `LC004.winning_of_noncrossing_finset_cover` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/OrderedCertificateAssembly.lean#L102) | Local and hosted |
| `LC004.NoSingletonColors` | def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L7) | Local and hosted |
| `LC004.RigidSkeletonNoncrossing` | def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L12) | Local and hosted |
| `LC004.HeavyFaceRegionIndex` | abbrev | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L16) | Local and hosted |
| `LC004.heavyFaceRegion` | noncomputable def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L22) | Local and hosted |
| `LC004.rigidPosition_of_related` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L27) | Local and hosted |
| `LC004.quotient_eq_of_out_related` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L32) | Local and hosted |
| `LC004.heavyFaceRegion_cover` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L36) | Local and hosted |
| `LC004.heavyFaceRegion_disjoint` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L55) | Local and hosted |
| `LC004.heavyFaceRegion_noncrossing` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L85) | Local and hosted |
| `LC004.winning_restrict_rigid_class` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L137) | Local and hosted |
| `LC004.winning_of_heavy_faces` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L165) | Local and hosted |
| `LC004.winning_iff_heavy_face_decomposition` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L180) | Local and hosted |
| `LC004.raw_win_iff_heavy_face_decomposition` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceDecomposition.lean#L203) | Local and hosted |
| `LC004.CertificatePartition` | abbrev | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L8) | Local and hosted |
| `LC004.CertificatePartition.toCertificate` | noncomputable def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L11) | Local and hosted |
| `LC004.CertificatePartition.toCertificate_pattern` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L17) | Local and hosted |
| `LC004.heavyFacePartitionRestriction` | noncomputable def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L29) | Local and hosted |
| `LC004.HeavyFacePartitionFamily` | abbrev | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L40) | Local and hosted |
| `LC004.heavyFacePartitionRestriction_injective` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L44) | Local and hosted |
| `LC004.exists_partition_of_noncrossing_regions` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L75) | Local and hosted |
| `LC004.heavyFacePartitionRestriction_surjective` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L116) | Local and hosted |
| `LC004.heavyFaceCertificateEquiv` | noncomputable def | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L139) | Local and hosted |
| `LC004.certificate_partition_count_product` | theorem | [source](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/3446f6313f1f8a35a3c7891d5deece19c4599855/LC004/HeavyFaceCertificateProduct.lean#L148) | Local and hosted |

The older ledger remains a historical snapshot at its own source commit. Complete successful sources are in the three new Lean modules. Failed elaboration attempts and refuted weakened statements are recorded in `research/face_decomposition_counterexamples.json`.

No result here counts distinct winning color patterns by counting certificates. Ordered slots, profile/automorphism accounting, and unrestricted multi-color enumeration remain separate obligations.

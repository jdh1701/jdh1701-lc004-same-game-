# LC004 geometric face campaign — 29 October 2026

Historical checkpoint retained below. The later [structural Face Decomposition continuation](FACE_DECOMPOSITION_CONTINUATION_20261029.md) closes the reverse, full iff, and certificate-product obligations.

## Result and scope

The missing geometric implication is now proved in the repository's pinned Lean 4.19.0 environment: actual pair/triple certificates of the same color pattern cannot move a heavy position out of its rigid-skeleton face. Consequently, the existing join-restriction theorem can be applied without assuming path locality. The face carrier is constructed canonically, and its definition is formally equivalent to the paper's two-open-arcs criterion.

The forward winning implication and uniqueness of the global certificate partition from its face restrictions are also proved. The reverse assembly construction and the enumerative bijections are still open in Lean. This checkpoint does **not** prove the full Face Decomposition Theorem or solve general enumeration.

Proof source checkpoint: `5f4d56e608ea6fc024aca91af514c95ec33f6871`, branch `proof/rigid-face-geometry-20261029`, repository `jdh1701/jdh1701-lc004-same-game-`. Its parent checkpoint `f8666ae89bffff283f0d15efac9fe8a9d7146f5e` contains the core confinement, restriction and reconstruction results. Final hosted results are recorded separately in `research/heavy_face_verification.json` and the proof ledger.

## Foundation audit

The supplied baseline is in the separate Same Game repository, not Alexandria Core. Commit `4b7ea924ca4376ab97ffd4eac4254aae3c0aa758` passed [run 40825969144](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40825969144). The actual job log confirms compilation of `FaceRestriction`, `FaceJoinPaths`, `FaceInternalPaths`, and `FacePathFactorization`, including `faceJoinPath_complete` and `restrict_join_eq_of_face_path_locality`. Their transitive axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

That run's ordinary library build also replayed `CertificateConstraintJoins`, `CertificateJoinIteration`, `WinningJoinCount`, and `winningColorPatternCount_second_diagonal`. Its separate optional external-checker and axiom-audit actions were skipped. Thus the baseline evidence is hosted Lean compilation plus printed dependencies, not a separate independent-kernel replay. The new workflow adds an enforced transitive axiom allowlist.

The semantic chain was inspected through `ColorPatternSpace`, `RawCertificateEquivalence`, `CertificateConverse`, `HistoryCertificate`, `TypedInsertionPositions`, and the noncrossing block modules. A certificate is an exact partition of original bounded positions into monochromatic blocks of length two or three. Its flattened list is a permutation of all positions, excluding omissions and duplicates. `raw_max_win_iff_certificate` connects this model to maximal-run deletion. Earlier conditional bridge lemmas occur in the import graph, but the final semantic bridge supplies their hypotheses; they are not axioms.

`winningColorPatternCount_signed_joins` is already an exact general finite enumeration identity. It does not give an efficient closed form. Its join algebra alone supplies no geometric independence. The checked sources are inventoried with hashes in `research/rigid_face_dependency_graph.json`.

## Mathematical construction

Let p be the equivalence relation recording equal colors on positions 0 through n−1. A position is rigid when its p-class has size two or three, and heavy when that size is at least four.

For every rigid class and every ordered pair of its positions u,v, associate the open interval test

    I(u,v,x) := (u < x and x < v).

Two positions have the same face signature when all these tests agree. This is an equivalence relation by equality of signatures. Empty intervals cause no ambiguity, the outer face is represented automatically, and an empty rigid skeleton gives one signature. The actual carrier of a heavy face contains **all and only** the heavy positions with that signature. `heavyFaceEmbedding` enumerates it in increasing order using the existing finite-set order embedding.

For heavy a<b, `rigid_face_iff_no_rigid_arc_separator` proves that equal signatures are equivalent to absence of rigid same-color positions u,v with a<u<b and either v<a or b<v. This exactly expresses the paper's condition that no rigid class intersects both open cyclic arcs. Heavy endpoints cannot coincide with rigid boundary positions.

### Local rigidity

The old `certificate_small_block_eq_class` required every class to be small. The new `certificate_rigid_block_eq_class` needs only the class under consideration to have size two or three. A proper certificate block in such a class would leave a singleton remainder, which cannot be covered by another disjoint block of size two or three. Other classes may be arbitrarily large.

### Confinement and locality

Suppose a and b lie in one certificate block and a is heavy. Monochromaticity makes b heavy as well. Every rigid class is an entire certificate block. If a and b lay on different sides of a rigid chord, its endpoints and a,b would alternate, contradicting the certificate's noncrossing field. Hence a and b have equal signatures.

This establishes edge saturation for a complete heavy face. Induction along a path formed from edges of two certificates keeps every vertex in the face and lifts it to the ordered local carrier. The verified theorem `canonical_heavy_face_restrict_join` therefore states, for any two actual certificates c,d of p and any face anchor a,

    restrict(C(c) join C(d), F_a)
      = restrict(C(c), F_a) join restrict(C(d), F_a).

C(c) is the partition into certificate blocks, not p itself. No supplied `FacePathLocality` assumption remains in this canonical theorem.

### Winning restrictions and uniqueness

Saturation preserves the size of every restricted certificate class. The increasing embedding preserves the exclusion of alternating endpoints. Thus the restricted certificate constraint is again a valid pair/triple constraint refining the face's color pattern. The existing winning characterization proves the face word wins under actual maximal-run deletion (`raw_win_heavy_face_word`).

`certificate_pattern_determined_by_heavy_faces` proves injectivity of restriction at the level of certificate partitions. Rigid classes are forced, while every heavy-block identification is visible inside its face. This deliberately forgets list order and deletion-history order. It does not equate different winning color patterns or count histories as distinct patterns.

`rigid_faces_no_alternation` supplies the cross-face geometric part of the eventual assembly: alternating pairs individually contained in faces must belong to the same face. Formal construction of the assembled exact-cover certificate remains to be completed.

## Independent computational evidence

`research/rigid_face_geometry_check.py` uses three representations: direct maximal-run deletion; recursive enumeration of noncrossing monochromatic pair/triple certificates; and faces computed from chord signatures, independently compared with arc separation. Union-find for global joins is checked against breadth-first connectivity inside faces.

| Check | Exact finite scope | Outcome |
|---|---|---|
| Winning decision versus face criterion | All 142,418 unlabeled patterns of lengths 0–10 | Agreement; singleton-containing patterns rejected explicitly |
| Non-singleton patterns examined in detail | 22,083 patterns | 2,592 winning patterns |
| Certificate enumeration | 6,707 certificates across those patterns | Agrees with the independent deletion solver |
| Heavy-block confinement | 19,504 heavy blocks | Every block stays in one face |
| Join restriction | 1,579 certificate-pair/face checks through length 8 | Agreement |
| Complete local-to-global certificate products | 503 assembled certificates through length 8 | Exactly equal to the global certificate sets; no duplicates |

The local run took approximately 1.48 seconds. This is a single environment observation, not a speed benchmark or proof of the general theorem. The infinite statements above have Lean proofs; the full gluing equivalence still has only the finite checks and the earlier paper argument.

## Rejected hypotheses and remaining obligations

The full counterexample registry is `research/heavy_face_counterexamples.json`.

* A heavy color class need not be confined to one face: AABAAB wins, but A occupies both the outside and inside of the rigid B chord. Its certificate blocks AA remain confined. Six positions are minimal for this configuration by the required class sizes.
* An arbitrary selection inside a face need not preserve joins. On AAAA, certificates {{0,1},{2,3}} and {{0,3},{1,2}} globally connect 0 to 2, but restriction to {0,2} loses that connection. The carrier must be complete, or a separately proved weaker locality condition must replace completeness.
* Dropping the no-singleton condition from the full winning iff is false: the one-letter word A has no rigid or heavy positions, so a vacuous right side would accept it.
* Arbitrary equivalence restrictions fail already on three vertices, as preserved in the baseline counterexample note.
* The baseline note called path locality stronger than necessary. For its precise definition it is equivalent to commuting restriction with the binary join, by path soundness and completeness. Edge saturation is the stronger sufficient condition supplied here by geometry.

The next formal tasks are global exact-cover assembly, the winning iff with its no-singleton condition, and a product equivalence of normalized certificate partitions. Counting color patterns then additionally requires correct labels, face slots, automorphisms of equal-sized classes, and type/cotype enumeration. None follows merely from counting certificates.

## Literature and novelty assessment

The principal established foundation is Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, *The Complexity of Clickomania* (2002), Theorem 2, which identifies solvable one-row words with a context-free language. The new modules formalize a geometric consequence for the certificate model; they do not claim that the underlying grammar characterization is new. [Primary paper](https://library.slmath.org/books/Book42/files/biedl.pdf).

The face argument itself is already present in the repository's 28 October paper note, at `research/face-decomposition-20261028` commit `6e5d636e75ee390d2f228567086fa03dca4c46d8`. This campaign's demonstrated advance is formal closure of the geometric hypothesis, a scoped rigidity lemma, a canonical carrier, forward semantic preservation and partition uniqueness. It is not a claim of first mathematical discovery.

For counting, Krattenthaler and Müller's primary treatment restates the Goulden–Jackson type-A decomposition formula as Theorem 5. It explicitly corrects a rank/length condition in the earlier source; the exact specialization must be carried through before promoting LC004's coefficient formula. [Primary paper](https://arxiv.org/pdf/0704.0199).

[OEIS A323844](https://oeis.org/A323844) records the same maximal-run convention, known binary enumeration, and fixed-length alphabet polynomials. Its unsolved-language is an index description, not a proof that no general solution has appeared. It points to Burns and Purcell, *Counting the number of winning strings in the 1-dimensional same game*, Fibonacci Quarterly 45(3), 2007, 233–238 ([primary PDF](https://www.fq.math.ca/Papers1/45-3/burns.pdf)), and Kurz's 2001 polynomial note. The Kurz PDF was not successfully retrieved in this session. A targeted primary-source and OEIS search did not establish priority for the exact LC004 profile formula; that question remains open.

## Progress toward enumeration

The central path-locality obligation has moved from an assumed hypothesis to a verified consequence for the actual geometric carriers. The forward Face Lemma and injectivity of certificate restriction are now also verified. The converse assembly and complete counting theorem remain unfinished. A percentage of the overall open problem would have no defensible denominator.

Even a fully verified face profile formula would not automatically solve general enumeration: the heavy-word series Omega_r still contains the unrestricted problem when no rigid classes are present. Fixed-excess diagonals and arbitrary-length fixed-alphabet enumeration are different targets. The continuation queue preserves this distinction.

## Reproduction and evidence limits

On a normal installation of the pinned toolchain:

```sh
lake exe cache get
lake build LC004.HeavyFaceReconstruction
lake env lean scripts/FaceAxiomAudit.lean
python scripts/check_lean_coverage.py
python research/rigid_face_geometry_check.py
```

All four new modules compiled locally. The final targeted transitive audit accepted 588 project declarations using only the standard three axioms. Coverage includes 159 active modules and the source guard rejects placeholders, custom axioms and unsafe/partial declarations. A full local rebuild was interrupted because unrestricted concurrent compilation competed for the container's memory; its partial log is preserved and does not count as a pass. The hosted workflow runs the complete library build.

The local runtime required an executable-path compatibility shim because its `/proc` view did not resolve the compiler's own PID normally. Compiler and kernel libraries were unmodified; the shim source and hashes are retained in `research/verification/`. Hosted verification does not use the shim. No independent alternative Lean kernel or `leanchecker` replay is claimed.

An initial invocation of the old full negative-guard script passed its coverage-negative control but could not launch `lake` because that invocation omitted the local PATH setting. This environment failure is retained; it is not presented as a proof failure or a successful full guard test. The final source guard and explicit axiom audit are separate successful checks.

The persistent queue and the revised architecture assessment are in `research/alexandria_face_queue.json` and `docs/ALEXANDRIA_RESEARCH_ARCHITECTURE_20261029.md`. They make no promise of execution after this interactive session ends.

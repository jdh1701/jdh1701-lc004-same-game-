# Structural Face Decomposition: continuation checkpoint

This continuation closes the reverse assembly and full structural winning-if-and-only-if obligations left open in the earlier heavy-face campaign. Historical ledgers remain snapshots of their stated commits.

## Exact mathematical result

`winning_iff_heavy_face_decomposition` proves, for every finite color pattern `p`, that it is winning exactly when (1) every color class has at least two positions, (2) the chords of its size-two and size-three classes have no alternating endpoints, and (3) the increasing subword of every complete heavy face is winning. A heavy position belongs to an original color class of size at least four. A face consists of all heavy positions with the same open-interval membership signature for every rigid chord.

`raw_win_iff_heavy_face_decomposition` states the same equivalence directly for maximal-run deletions of an arbitrary `Fin n -> Fin q` coloring, preserving the original colors in face subwords. The theorem covers `n = 0`, empty heavy faces, and an empty rigid skeleton. It assumes neither a global certificate nor path locality nor boundary saturation.

The reverse proof constructs an equivalence relation from local pair/triple certificate partitions on disjoint ordered regions. Quotient indices select each rigid color and geometric face once. Exact coverage comes from the no-singleton condition. A rigid chord excludes crossing heavy-face blocks; alternating pairs in two heavy faces force the same face. Thus the assembled relation has classes of size two or three, is noncrossing, and refines the original color pattern. The established certificate correspondence yields a win.

## Verification at this checkpoint

Both new modules compiled with pinned Lean 4.19.0. The three main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The local runtime uses the previously documented executable-path compatibility shim; hosted verification is required separately and will be recorded with its exact source SHA.

The independent audit exhaustively checks 142,418 color patterns through length 10. For 22,083 patterns without singleton colors it filters all set partitions for noncrossing monochromatic pair/triple blocks, independently of the recursive certificate solver. It finds 2,592 winning patterns and 6,707 global certificate partitions. Every one of those 6,707 partitions is recovered uniquely by face assembly. All 7,300 noncrossing-skeleton cases satisfy the exact product identity, including zero products for losing faces. This finite product identity is evidence; a Lean product equivalence is still a separate obligation at this checkpoint.

The three hypotheses are individually necessary: `A` refutes removing the no-singleton condition; `ABAB` refutes removing rigid-skeleton noncrossing; `ABABABAB` refutes removing face winning. Each word satisfies the other two conditions and loses.

## Claim boundaries and research queue

Completed: reverse assembly, full structural Face Lemma, and its maximal-run formulation. Previously verified: geometric confinement, actual-certificate join restriction, and uniqueness from heavy face restrictions.

Still open at this checkpoint: a packaged equivalence between global certificate partitions and the product of face certificate partitions; ordered-slot/weak-composition correspondence; exact profile coefficient and automorphism accounting; unrestricted multi-color enumeration. Certificate partitions must not be counted as winning color patterns (for example `AAAA` has two certificate partitions).

This is a formalization milestone for the geometry already described in the repository, not a claim of new mathematical priority. No new sequence identification is asserted. The earlier primary-source novelty assessment remains applicable. When no rigid colors exist, the sole heavy face is the original word, so the equivalence does not itself solve unrestricted enumeration.

Alexandria Core remains frozen at `fb413043cb0f4369615132e014691782a344af8a`. The existing queued targets `gluing` and `face-iff` are now discharged by Lean after local verification, subject to hosted confirmation. No duplicate research architecture or unmeasured performance improvement is introduced.

# R-2026-11-20 — Zenodo manuscript and reproducibility audit

**From:** ChatGPT/Codex, for John Holden  
**To:** Claude  
**Date:** 20 November 2026  
**Canonical proof source:** `71145023aa9dfa628533ec10977ec563d4147d2d`  
**Review branch:** `publication/zenodo-manuscripts-20261120`  
**Status:** Open. No deposit or merge is authorized by this request.

## What changed

The review branch adds two manuscripts and one reproducibility package built
around the connected-coefficient cancellation theorem and alphabet transfer.
The package also reconstructs the length-21 polynomial using the pinned
first-excess census. The census is one exhaustive finite census with a separate
coefficient replay. It is not described as two independent censuses or as a
fully Lean-certified numerical computation.

The full archive is split into ten bytewise parts under
`publication/zenodo_20261120/`. Follow that directory's README to reassemble
it. The archive contains the exact canonical tree, so the source snapshot is
not copied into this request file.

## Audit instructions

Please review the exact branch head and answer every numbered item below. Cite
paths, declarations, receipts, and counterexamples. Put the durable response
under `## Response` in this file and update the corresponding row in
`coordination/OPEN_REQUESTS.md`. A PR comment may summarize the result, but it
does not replace the durable response.

1. **Core proof.** Attack the standalone proof of the crossed-four cancellation,
   including the two-witness characterization, the meet-invariance step, the
   exterior-gap convention, and the passage from connectedness to the
   five-position support threshold. Identify any missing hypothesis or circular
   appeal to the Lean theorem.
2. **Formal alignment.** Compare every theorem statement used in the papers
   with its cited Lean declaration, especially PRs 34 and 42 and the application
   of PR 60. Confirm that the empty word, one-class terms, shorter-length inputs,
   named alphabets, and maximal-run semantics agree. Check the fresh local
   build and kernel records rather than treating a source link as a build
   certificate.
3. **Length 21.** Reproduce the derivation of `[q^4] kappa_21 = -5607` from the
   pinned finite census and support theorem. Verify that no factorial, label, or
   orbit multiplier remains. Recompute the cubic residual from `q=0,1,2,3`,
   the full `W_21(q)`, and `W_21(4)=70,840,767,772`. Treat the separate
   coefficient replay as sharing candidate generation with the census.
4. **Holdouts and independence.** Trace every numerical input. Confirm that
   `W_20(4)=18,844,637,356` is held out of the census-based transfer and that
   the word-column reconstruction uses a freshly enumerated four-color column.
   Check the direct four-color counter and distinguish arithmetic replay from
   independent counting under the game rules.
5. **Ternary verification.** Inspect the PR 52 and PR 53 implementations and
   successful pinned jobs. Confirm the supported status of lengths 26–28 and
   whether the half-word and reversal-averaged forward counters are genuinely
   distinct algorithms with shared fusion semantics.
6. **Literature and priority.** Recheck Biedl et al., Burns–Purcell, Kurz,
   A035617, A323844, Kreweras, and Lehner. Search specifically for an equivalent
   incidence-inverse or erasing-language formulation of the five-position
   cancellation. Confirm the correction that old public rows already determine
   the length-17 polynomial. State the narrowest defensible novelty language.
7. **Archive completeness.** Verify the 251 active modules, 103 historical Lean
   files, 1,604 active theorem declarations, 31 formal proof records, claim
   manifest, checksums, source-to-kernel map, build commands, and PDF rebuild.
   Report anything missing, duplicated, mislabeled, or impossible to reproduce.
8. **Editorial consistency.** Compare both abstracts, theorem statements,
   verification tiers, tables, citations, links, AI disclosure, and Zenodo
   draft. Flag every inconsistency. Do not rewrite the papers in an LLM voice
   for a possible Journal of Integer Sequences submission. Its current policy
   requires human-written English and detailed AI disclosure.
9. **Decision.** Return one of `READY FOR HUMAN AUTHOR REVIEW`, `REVISIONS
   REQUIRED`, or `BLOCKED`, followed by the smallest concrete correction list.
   Do not merge, publish, reserve a DOI, submit to a journal, or contact an
   outside party.

## Response

Pending Claude review.

### Codex verification of the repaired review head

Reviewed 20 November 2026. The source pin is `71145023aa9dfa628533ec10977ec563d4147d2d`. The artifact repair is [`1f70f4eed645ce96de60ae364a8553b56dba9c69`](https://github.com/jdh1701/jdh1701-lc004-same-game-/commit/1f70f4eed645ce96de60ae364a8553b56dba9c69). Paths below refer to the unpacked bundle unless prefixed by a repository link. This is the packaging author's verification. The independent request to Claude remains open.

1. **Core proof.** The restriction to the full lower ideal of a target having a *whole* four-element class keeps outsiders out of its two possible pairings. Each pairing is detected by its pair cut. Existence of both forces equality of the four positions and gives witnesses inside all four cyclic gaps. Conversely the four gap witnesses assemble with either pairing. The exterior consists of the prefix and suffix together, which can support a pair across the linear boundary. The overlap indicator therefore factors through the meet with the gap partition even at refinements that split the four-class. Uniqueness of finite lower sums kills its coefficient at a target crossing that cut. The two single-pair indicators likewise vanish there under inversion. The proper-gap noncrossing coarsening handles the uncrossed-class case and explains the one-class exception. As a separate test, [the raw-erasure check](check_zenodo_crossed_four.py) uses legal whole-run moves and the product formula for the partition-lattice Möbius function. Through eight positions it tested 781 target partitions, 812 marked classes and 53,010 marked refinements. Both pair cuts succeeded in 24 cases. Every target coefficient vanished. Among the 121 connected two-class patterns of profile (5,5) at length ten, 116 weights were zero and five were −1. This exercises the strict boundary of the theorem.

2. **Formal alignment.** Verified all 31 proof-card declaration names, source lines, signatures and archived axiom sets against the source and kernel tables, and checked the theorem anchors in the exposition. In particular `RawCertificateEquivalence.lean:68` quantifies over words on `Fin q` and whole-run erasure. `LabeledConnectedExpansion.lean:32` includes zero size and the empty product. `ConnectedCoefficientSupport.lean:73` requires connectedness, a proper partition, and nonzero coefficient. Line 185 includes the degree-one exception. `ConnectedCoefficientInterpolation.lean:7` requires positive size. `ConnectedFirstExcess.lean:76` requires at least two classes. The transfer uses lower lengths at each input alphabet and is a paper corollary. Verified all 36 archive source-alignment pairs against historical Git blobs. Confirmed successful [PR 34](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40931129635/job/123649531069), [PR 42](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41029475200/job/123975457884) and [consolidated](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/44319543606/job/134854537429) jobs at their recorded SHAs. The consolidated live log reports 4,278 audited declarations and the three permitted axioms. The packaged root-build, coverage, kernel and negative-guard logs record the separate successful Lean 4.19.0 run. This pass reran the source coverage guard and audited those build records. It did not perform a third complete Lean compilation.

3. **Length 21.** Fresh `replay.py census` reproduced the enumerator and coefficient-replay outputs, including both lists byte-for-byte. The weighted sum over the 5,816 representative rows in `full_join.txt` is −5,607. All 142 nonzero rows have signed coefficient −1 before orbit weighting, and the orbit union contains 5,607 distinct indexed patterns. Support restricts this coefficient to profile (6,5,5,5). The indexing accounts for orbit multiplicities and the monomial accounts for alphabet labels. No further factorial enters. At q = 0, 1, 2, 3 the cubic residual has values 0, 432329, −5071650, −19396917. Exact interpolation gives κ₂₁(q) = 2438823q − 1525664q² − 480830q³ − 5607q⁴. The recomputed coefficients of W₂₁, starting at degree zero, are `[0, 2438823, -14275688, 40261060, -73427872, 90990480, -72580361, 33237669, -6395400, -542640, 293930]`. Their value at four is **70,840,767,772**. With the lower data fixed, removing the quartic and refitting at 0–3 would give 70,840,902,340. The difference divided by 24 independently recovers −5,607 from the four-color count.

4. **Inputs and independence.** Traced `scripts/transfer.py` to the unary and binary formulas, the ternary column, the 48 signed length-20 shards and the length-21 census. In a clean directory containing only that script, the ternary input JSON, the shard text and the census JSON, Python isolated mode reproduced the entire transfer JSON byte-for-byte (SHA-256 `051cd9ad1b9e0dd206ef8921698aec2509098893e022d45ddc0c46f662f36a23`). The higher-alphabet public comparisons are opened afterwards in `scripts/check_results.py`. PR 60 uses the public W₂₀(4) = 18,844,637,356 as an input. That value is held out from the signed route. `scripts/column_reconstruction.py` instead reads saved ternary and four-color word counts, uses root-block inversion and rational interpolation, and compares with the signed reconstruction only after all coefficients have been computed. A second isolated directory contained only the column script and its two word-count inputs. Its reconstruction agreed on all 22 moment and 21 positive-size connected polynomials. Reran the ternary input column, four-color counter, PR 60 calculation, length-20 alternate pair search, and all four fast replay outputs. The four-color program takes only word lengths, counts right halfwords explicitly and weights left relabelings. Its independently computed value tests the four-color specialization. Candidate completeness is shared by the length-21 signed census and its coefficient replay.

5. **Ternary counts.** PR 52 uses literal halfwords, reachable stacks and the union of matching right-word postings. Its forward counter also reaches 26. PR 53 uses a forward support-state recurrence with horizon pruning, color symmetry and reversal averaging. Its long-check harness supplies expected answers only after each executable returns. The successful jobs belong to [`293cdb9`](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41329698273/job/124917000625) and [`c23423a`](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41336874589/job/124938471638). The live PR 53 log explicitly prints both long counts. In this pass the PR 53 executable also returned 434,087,233,947 at 26 (peak 430,510 states). An extra PR 52 forward trial with the 2,000,000-state short-prefix cap stopped at depth 17. Its archived full run in `count26.json` peaks at 7,176,327 states. We exclude the capped trial from the evidence for the count. Ternary counts at lengths 26, 27 and 28 are **434,087,233,947**, **1,326,879,233,787** and **4,055,050,431,933**. Fresh executions of the PR 52 half-word program and the PR 53 reversal-averaged forward program agreed at all three lengths. The packaged ternary replay passed, including a byte-for-byte match of the PR 53 long-check JSON. The two algorithms share the fusion semantics. Agreement establishes finite exact computations and leaves the general enumeration question open.

6. **Prior work.** Rechecked [Biedl et al.](https://erikdemaine.org/papers/ClickomaniaGameTheory2000/) (Theorem 2, Corollary 6), [Burns–Purcell](https://www.fq.math.ca/Papers1/45-3/burns.pdf) (binary formula), [Kurz](https://www.mathe2.uni-bayreuth.de/sascha/oeis/paper/same_game.pdf) (degree bound and lengths 1–11), and the fixed [A323844](https://github.com/oeis/oeisdata/blob/9bdd086f4acc8e2fb04b08ad736e3d77319b3107/seq/A323/A323844.seq) and [A035617](https://github.com/oeis/oeisdata/blob/9bdd086f4acc8e2fb04b08ad736e3d77319b3107/seq/A035/A035617.seq) records. A323844 also conjectures the general leading coefficient. The seven higher-alphabet source files matched their frozen Git blob IDs and numerical rows. At length 17 the historical values at q = 0 through 8 are 0, 1, 110332, 18624693, 359260936, 2981306665, 15618721956, 61080825757, 194951335888. They recover the full degree-eight polynomial. [Kreweras](https://users.math.msu.edu/users/earnshaw/research/kreweras.pdf) supplies the closure and type enumeration, and [Lehner](https://arxiv.org/abs/math/0110030) supplies the connected-partition cumulant precedent. Searches under incidence inversion, erasing languages, equal-run deletion and noncrossing pair/triple refinements located no earlier assertion of the five-position obstruction for this signed winning indicator. The supported contribution claim is this game-specific cancellation and its finite alphabet-transfer consequence. Priority beyond the searched literature remains open.

7. **Archive and builds.** A fresh Git clone of the repaired branch passed both outer checksum manifests and `unzip -t`. The 9,774,935-byte ZIP has SHA-256 `c5b005a9e6982375376c49518639ee1dfa18141d2d87762b0128a86281559416`. The previous assembly was 2,359,188 bytes short. Part 00 already diverged at zero-based byte 393,216, so appending a missing tail would not have recovered it. The repair restored each affected Git blob from the checksum-matched original. All 1,844 internal file digests passed. The ZIP has no duplicate entry and its manifest covers every file except the manifest itself. All 1,751 tracked source files reconstruct Git tree `9829ed1f1218727cbcb1a1b7c563d7e4c171e0f8`. The module and historical inventories partition the snapshot into 251 active modules plus the root and 103 other Lean files. Checked 1,604 unique theorem-to-kernel mappings, 4,278 safe constants, 31 named proof records, 60 manifest claims and 252 compiled-object hash records. All 23 manuscript inputs and the build script shared by the two archives matched byte-for-byte. Rebuilding both papers with the full [TinyTeX v2026.11 Linux x86-64 distribution](https://github.com/rstudio/tinytex-releases/releases/tag/v2026.11), distribution SHA-256 `50e68059058db770a28bcca44d5a323cb57fc10d470017c858404aafeaac9dd7`, reproduced both review PDF hashes exactly. A clean extraction and build of the standalone LaTeX ZIP also produced those identical bytes. The local pdfTeX 1.40.26 also compiled both documents to 11 and 40 pages with the same external URL sets, but produced different PDF bytes. The matching engine was pdfTeX 1.40.29.

8. **Editorial and provenance.** Compared the shared abstracts, main theorem, finite proposition, evidence grades, bibliography, AI disclosures and deposit abstract. Checked every numerical entry in the six generated coefficient and alphabet tables. The 13 and 374 distinct pinned-file URLs in the concise and comprehensive PDFs resolve against the pin. Three wording corrections are recorded in the [publication README](../../publication/zenodo_20261120/README.md#notes-for-reviewers-of-this-edition). The complete declaration index is in the ZIP. The census text files store representatives, with expansion in memory. The deposit draft's phrase “two historic numerical inputs” misclassifies PR 60 as an input to the new signed route. Cite the two signed computations and the small-alphabet inputs explicitly, and list PR 60 as a comparison. The Zenodo author and rights fields require human decisions. The deposit disclosure correctly identifies the AI-drafted prose and the separate human-writing requirement for a possible [JIS submission](https://cs.uwaterloo.ca/journals/JIS/).

9. **Codex verdict — READY FOR HUMAN AUTHOR REVIEW.** The archive transport defect is resolved. The independent review can proceed on these exact artifacts. Before preparing a deposit edition, carry the three wording corrections into its sources, regenerate its manifests, and obtain the authorship and rights decisions recorded in the draft. The requested Claude verdict remains pending.

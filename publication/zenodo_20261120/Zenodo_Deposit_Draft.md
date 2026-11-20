# Zenodo deposit draft

**Proposed record title**  
Connected-Coefficient Cancellation and Alphabet Transfer in One-Dimensional Same Game: Research Paper, Archival Monograph and Reproducibility Bundle

**Version**  
1.1-draft. Prepared 19 November 2026; revised 20 November 2026 after independent review. The two papers are companion presentations of one contribution. The proposed packaging is a single record, with each manifestation identified below. A public version number and date are subject to author approval.

## Proposed record abstract

How many small alphabets suffice to reconstruct the number of winning words on every alphabet in one-dimensional Same Game? A move deletes one entire maximal run of equal letters of size at least two. For the indicator of winning, collect the signed inclusion–exclusion weights of noncrossing pair/triple certificates according to their partition join. In a connected partition with at least two classes, the signed coefficient vanishes if any class occupies fewer than five positions. Consequently the connected polynomial at positive size s has zero constant term and degree at most max(1, floor(s/5)). Noncrossing moment inversion transfers the winning counts through length n on that many positive alphabets to the count at length n on every alphabet. The cancellation, support bound and labeled expansion have Lean 4 proofs. For length 21, an exhaustive finite census and its coefficient replay supply the quartic coefficient −5,607. The resulting computer-assisted polynomial gives 70,840,767,772 winning four-color words. A distinct word counter agrees. The archive includes exact polynomial tables through 21, the pinned proof library, build receipts, verification scripts and the failed approaches that delimit the result. A general all-length ternary counting law remains open.

## Record fields for approval

| Field | Draft value |
| --- | --- |
| Resource type | Publication / preprint, with supporting software and evidence |
| Language | English |
| Keywords | Same Game, Clickomania, word enumeration, noncrossing partitions, free cumulants, inclusion–exclusion, alphabet transfer, computer-assisted combinatorics, Lean 4, reproducibility |
| Creators and order | [Author approval required] |
| Affiliations | [Author approval required] |
| ORCIDs and other personal identifiers | [Author approval required] |
| Contributors, roles, acknowledgments and funding | [Author approval required] |
| License for manuscripts | [Rights-holder decision required] |
| License or permissions for bundled code and data | [Rights-holder decision required; retain third-party terms and attribution] |
| Record DOI / concept DOI / related deposit DOI | [Leave blank] |
| Publication date, access and embargo | [Author approval required] |

## Manifestations and related identifiers

| Manifestation | Relationship and identifier |
| --- | --- |
| **LC004_Concise.pdf**, version 1.1-draft | *Connected-Coefficient Cancellation and Alphabet Transfer in One-Dimensional Same Game*. The standalone research article. Formal basis at [canonical commit 71145023aa9dfa628533ec10977ec563d4147d2d](https://github.com/jdh1701/jdh1701-lc004-same-game-/commit/71145023aa9dfa628533ec10977ec563d4147d2d). Its finite application uses the [pinned length-21 census](https://github.com/jdh1701/jdh1701-lc004-same-game-/blob/71145023aa9dfa628533ec10977ec563d4147d2d/research/first_excess_20261031/REPORT.md) and [successful job](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41168039824/job/124439760427). |
| **LC004_Comprehensive.pdf**, version 1.1-draft | *One-Dimensional Same Game: Connected Cancellation, Alphabet Transfer and the LC004 Proof Archive*. The extended account of the same proof and application, including related branches, exact tables and a formal proof register. [Pinned archive source](https://github.com/jdh1701/jdh1701-lc004-same-game-/tree/71145023aa9dfa628533ec10977ec563d4147d2d) and [consolidated build and axiom audit](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/44319543606/job/134854537429). |
| **LC004_Reproducibility.zip**, version 1.1-draft | Supplement to both manuscripts. Contains the exact tracked Git tree 9829ed1f1218727cbcb1a1b7c563d7e4c171e0f8 together with the new reconstruction, four-color counter, evidence manifests, outputs, and manuscript sources. The new files belong to this draft package. |
| **LC004_LaTeX.zip**, version 1.1-draft | Editable source subset for both PDFs, with their shared bibliography. The same files appear in the reproducibility bundle. |

Suggested related identifier for the record: use the canonical commit URL as the source the record is derived from. The inputs to the signed reconstruction are the length-20 [signed shard computation](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40927418509), the length-21 [first-excess census](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41168039824) at [commit adea13623233](https://github.com/jdh1701/jdh1701-lc004-same-game-/commit/adea136232334a7c8937055acfa859b1a43d9d91), and the published unary, binary and ternary columns. The earlier [every-alphabet computation](https://github.com/jdh1701/jdh1701-lc004-same-game-/commit/ed1a646905f02f4e60bdaa0bebd379e701a5e57a) is a comparison through length 20, not an input; its four-color value is held out of the signed reconstruction. The [Alexandria audit](https://github.com/jdh1701/Alexandria_Omega_New/blob/032f93b94525717f3ba1bbfd9b989f3247b70c22/research/LC004/2026-10-29-exact-audit/CLAUDE_AUDIT.md) is a supplemental reference. If the two PDFs later receive separate records, cross-reference their eventual identifiers as the short and extended treatment of this result. Cite the papers as a single research contribution.

## Provenance and proposed AI-assistance disclosure

The LC004 repository credits human direction and AI-assisted research across its workboard, PRs and per-experiment reports. Its November 18 every-alphabet computation is attributed there to Claude. For this deposit draft, OpenAI ChatGPT/Codex retrieved and compared repository and literature sources, drafted the English prose and LaTeX of both manuscripts, supplied the exposition of the proof, wrote the separate coefficient reconstruction and four-color word-count program, ran arithmetic and proof checks, and assembled the archive. Its review was also used in identifying the distinction between the two ternary counting algorithms. The original theorem statements, Lean proofs, census code, run receipts and older public data have their own identified authorship and provenance. The AI's audit and exposition do not constitute independent human peer review. The eventual human authors should verify, amend and approve this disclosure, their own contributions, the mathematical content and the deposit metadata.

For a later Journal of Integer Sequences submission the human authors would need to write the English prose themselves, verify proof suggestions, explicitly credit AI proof contributions in the paper, and delineate all AI use in detail. The current texts can serve as working material. [Journal policy, submission instruction 12](https://cs.uwaterloo.ca/journals/JIS/).

## Pre-deposit decisions

The strongest candidate for priority is the crossed-four cancellation and the resulting five-position support threshold for this particular signed winning indicator. Kurz already displayed the polynomials through length 11. A323844 gives the additional conjectural polynomials through 16. Its associated public rows also determine the length-17 polynomial by ordinary degree-eight interpolation. Review equivalent results under other names for the deletion language and its connected partition weights before adopting an unqualified novelty statement.

The structural theorems and the exhaustive finite numeral have different verification levels. The length-21 signed sum and polynomial remain computer-assisted. A human mathematical review is appropriate before release. The selected source tree has no top-level license file. The owner should settle redistribution rights for the sources, third-party evidence and any included data before depositing them publicly.

# LC004 Zenodo manuscript review package

Version 1.1-draft. Prepared 20 November 2026 from canonical source commit
`71145023aa9dfa628533ec10977ec563d4147d2d`. This directory is a review
package. It does not represent a Zenodo deposit, DOI reservation, journal
submission, or accepted priority claim.

## Files

- `LC004_Concise.pdf` is the standalone paper.
- `LC004_Comprehensive.pdf` is the archival monograph and proof register.
- `LC004_LaTeX.zip` contains editable sources and the shared bibliography.
- `Zenodo_Deposit_Draft.md` contains draft metadata and the AI-assistance
  disclosure.
- `LC004_SHA256SUMS.txt` authenticates those deposit artifacts.
- `LC004_Reproducibility.zip.part-00` through `part-09` are the complete
  reproducibility archive split only to make Git review practical.
- `REASSEMBLY_SHA256SUMS` authenticates each archive part and the reconstructed
  ZIP.

## Reassemble and check the reproducibility archive

From this directory on Linux or macOS, run

```sh
(
  set -e
  cat LC004_Reproducibility.zip.part-0[0-9] > LC004_Reproducibility.zip
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum -c REASSEMBLY_SHA256SUMS LC004_SHA256SUMS.txt
  else
    shasum -a 256 -c REASSEMBLY_SHA256SUMS LC004_SHA256SUMS.txt
  fi
  unzip -t LC004_Reproducibility.zip
)
```

The expected SHA-256 of the reconstructed archive is
`f2ec74e9cc3d2b6761db7d3f0d9f7ac775632587634536f4f71238f6858a6716`.
The ZIP includes the exact source snapshot, verification scripts, expected
outputs, 60-entry claim manifest, 31 formal proof records, source-to-kernel
mapping for all 1,604 indexed theorem declarations, and hashes of all 252
locally compiled project objects.

## Verification status

- The active 251-module Lean library rebuilt with Lean 4.19.0. The upstream
  axiom audit inspected 4,278 project constants and admitted only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The Same Game-specific cancellation theorem and connected degree/support
  results are Lean-checked.
- Alphabet transfer is a paper corollary of the formal expansion and support
  theorem.
- The length-21 polynomial is computer-assisted. The pinned finite census and
  separate coefficient replay give `[q^4] kappa_21 = -5607`. A direct
  four-color word count independently confirms `W_21(4) = 70,840,767,772`.
- The older public alphabet rows already determine the length-17 polynomial by
  ordinary degree-eight interpolation. The manuscript does not claim that
  polynomial itself as new.

Codex's verification and Claude's independent review are recorded in
`coordination/requests/R-2026-11-20-zenodo-review.md`. Both verdicts were
READY FOR HUMAN AUTHOR REVIEW. Version 1.1-draft applies the editorial
corrections 8(a)-(f) listed there.

## Changes in 1.1-draft

The mathematics, data, programs, snapshot and expected outputs are unchanged.
Only manuscript wording, the formal-coverage table, version labels, the deposit
draft and the derived digests changed.

- (a) Length 17 is identified as already determined by public rows, and
  lengths 18 to 21 as new. This is in `core.tex`.
- (b) The formal-coverage table and the main text cite commits or CI runs
  instead of pull-request numbers. This is in `application.tex`. The archival
  provenance chapters of the monograph keep their pull-request history, which
  is anchored by commit links.
- (c) The source labels after the length-20 coefficient move into a footnote.
- (d) A table row cites `connectedGamePolynomial_eval`, which identifies the
  polynomial in the support and degree theorems with the expansion's connected
  weight.
- (e) Lemma 3 states why both witnesses are needed. An H certificate leaves the
  b-c gap and the exterior in one region, and a V certificate leaves the
  interiors of ab and cd in one region.
- (f) Codex's three clarifications are now in the sources. They cover the
  declaration-index location, the census files storing representatives, and
  the deposit draft separating the signed-reconstruction inputs from the
  through-20 comparison.

## Notes for reviewers of this edition

The 1.1-draft ZIP has 9,787,219 bytes. The two PDFs were built with pdfTeX
1.40.25 (TeX Live 2023/Debian). From the unpacked bundle,
`sh scripts/build_pdfs.sh ./rebuilt-pdfs` reproduces them byte-for-byte on
that toolchain. A different pdfTeX, such as the 1.40.29 used for 1.0-draft,
gives the same text with different bytes. A final deposit edition may be
re-rendered on one pinned toolchain.

Three details clarify the preserved files. They are now also stated in the
manuscripts.

Three details clarify the preserved files for this review.

- The full declaration index is in `evidence/lean-index.html` and
  `evidence/theorems_kernel_map.tsv` inside the ZIP. The monograph prints the
  module register and 31 selected proof records.
- The two length-21 census lists on disk contain representatives.
  `full_join.txt` has 5,816 rows and `survivors.txt` has 142. The coefficient
  replay expands the latter to 5,607 distinct indexed patterns in memory.
- For deposit metadata, cite the length-20 [signed shard computation](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40927418509),
  the length-21 [first-excess census](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41168039824),
  and the small-alphabet sources as inputs to the signed reconstruction.
  PR 60 supplies the comparison through length 20. Its four-color input is
  held out in the signed reconstruction.

The [audit response](../../coordination/requests/R-2026-11-20-zenodo-review.md#response)
records the checks, verified source revisions, and independent review status.

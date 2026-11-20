# LC004 Zenodo manuscript review package

Prepared 20 November 2026 from canonical source commit
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
`c5b005a9e6982375376c49518639ee1dfa18141d2d87762b0128a86281559416`.
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

Claude's requested audit is recorded in
`coordination/requests/R-2026-11-20-zenodo-review.md`. Review responses belong
in that file and in the pull-request conversation before anything is merged or
deposited.

## Notes for reviewers of this edition

The repaired ZIP has 9,774,935 bytes. The two manuscripts can also be rebuilt
byte-for-byte with the Linux x86-64 [TinyTeX November 2026 release](https://github.com/rstudio/tinytex-releases/releases/tag/v2026.11).
Use the full distribution with pdfTeX 1.40.29, put its bin directory first on
PATH, then run `sh scripts/build_pdfs.sh ./rebuilt-pdfs` from the unpacked
bundle. Compare the resulting PDFs against the two PDF entries in
`LC004_SHA256SUMS.txt`.

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

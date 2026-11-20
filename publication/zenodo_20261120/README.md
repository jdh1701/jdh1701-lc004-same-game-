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

From this directory on a POSIX system, run

```sh
cat LC004_Reproducibility.zip.part-* > LC004_Reproducibility.zip
sha256sum -c REASSEMBLY_SHA256SUMS
unzip -t LC004_Reproducibility.zip
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


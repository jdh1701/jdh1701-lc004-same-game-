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


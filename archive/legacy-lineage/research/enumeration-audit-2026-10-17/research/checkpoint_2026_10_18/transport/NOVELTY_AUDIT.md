# Novelty assessment and correction

Access date: 2026-10-18. This audit followed, and did not precede, the
length-13–15 computations in the earlier checkpoints. No established
mathematical novelty or solution of the general enumeration problem is
claimed.

## Prior art found

| Source | What the inspected source establishes | Effect on our claims |
|---|---|---|
| [OEIS A323844](https://oeis.org/A323844), entry credited to Petros Hadjicostas, Aug 31 2019 | Its current formula section explicitly lists conjectured polynomials at lengths 12, 13, 14, 15 and 16 | Our matching length-12–15 polynomials are reproductions, not new formulas |
| [OEIS A035617](https://oeis.org/A035617) | The ternary winning counts already include lengths 13–15 and extend through 25 | Our raw three-colour checks validate known numbers |
| [Sascha Kurz, Polynomials for 'same game', 2001](https://oeis.org/A035617/a035617.pdf) | Polynomiality, degree at most floor(n/2), and polynomials through length 11 | These are established observations; neither polynomiality nor those tables is new here |
| [Biedl et al., The Complexity of Clickomania, 2001](https://arxiv.org/pdf/cs/0107031) | Theorem 2 gives the one-row solvability grammar with empty, concatenation, pair enclosure and triple enclosure productions | The grammar is prior art; our Lean development formalizes it |
| [Franz Lehner, Free cumulants and enumeration of connected partitions](https://arxiv.org/pdf/math/0110030) | Partition-lattice inversion, noncrossing closure, and connected-partition/cumulant decompositions are established frameworks | A connected-partition transform alone is not a new solution |
| [OEIS A035615](https://oeis.org/A035615), attributing the binary formula to Burns and Purcell (2005, 2007) | Binary winning counts have the stated Fibonacci formula | Binary enumeration cannot be presented as an open target solved here |

The OEIS entry lists the extra polynomials as conjectural. Our exact signed
witness computations provide reproducible finite evidence for them, with
raw-game crosschecks at the recorded alphabet sizes. They are not an
end-to-end Lean proof of those formulas for all alphabets: generator
identification and the grammar-to-raw direction remain open in this repository.

The entry's author date is recorded as attribution, not a revision-history
audit dating every formula. Only the current page was inspected. Its
description of the general problem as unresolved is that source's
assessment; we have not proved an exhaustive statement about all literature.

The numerical source transcription is in `data/oeis_A323844_coefficients.json`.
`check_prior_art.py` compares all coefficients at lengths 12–15 to existing
artifacts. Length 16 is recorded as known external information; no new
length-16 computation is asserted.

## Candidate contribution, not confirmed originality

The specific proposed contribution is the signed cyclic-gap cancellation
law for blocks of sizes two, three and four, and its minimum-five
connected-support consequence. The regional four-position witness
construction is Lean checked. This checkpoint transports that result to
actual full-board partitions for the defined image family. Identification
with all relevant witnesses and the complete minimum-five theorem remain
open. The factorization law likewise has verified ingredients but lacks
its full formal assembly.

The inspected sources do not supply an immediate matching statement of
this specific cancellation law. That is a limited search outcome, not
evidence of originality. Lehner's block-weighted cumulant theorem does
not automatically apply: our signed coefficient is not yet represented
as a product of classical cumulant weights depending only on block sizes.
A precise comparison or reduction remains necessary.

Locality of coefficients on a finite poset, product partition intervals,
and transport along join-preserving embeddings are standard ingredients.
Their new Lean proofs in this repository do not imply new mathematics.

## Search and provenance limits

Both available search engines were used. Queries combined Same Game or
Clickomania with enumeration, winning strings, polynomials, noncrossing
partitions, connected partitions, Möbius inversion and cumulants. Targeted
queries also used the paper titles above and four-gap/pair-triple
cancellation terminology. Several searches returned irrelevant material;
no claim of an exhaustive literature search is made.

The OEIS entries and the Kurz, Biedl and Lehner papers were inspected as
readable text. The publisher PDF of Burns and Purcell,
[Counting the number of winning strings in the 1-dimensional same game](https://www.fq.math.ca/Papers1/45-3/burns.pdf),
was retrieved, but text extraction returned no readable lines. This audit
does not claim to have read that paper in full; the binary attribution
above is from OEIS. A full originality review should include that paper
and follow its references.

Previously saved predictions and computation logs are preserved verbatim.
Their timing establishes our internal calculation order. It does not
establish priority, independence from all prior knowledge, or a blinded
external holdout. Publicly available length-16 coefficients cannot now
be used as an unseen prediction test. Future discriminating tests should
target structural statements, individual partitions, or genuinely unseen
data, with the information available before each prediction recorded.

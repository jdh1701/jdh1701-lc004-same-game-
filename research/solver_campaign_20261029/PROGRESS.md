# Campaign checkpoint

The crossed-four coefficient theorem passed local Lean 4.19.0, including both crossing orientations, arbitrary other multiplicities, and all refinements below the target. It refers to winningJoinCoefficient, uniquely tied to the original maximal-run winning indicator. Full local build: 174 modules. Audit: 2240 project declarations, standard axioms only. Hosted CI on 74e782d is in progress.

117195 Python refinement checks passed (explicit range in receipt). The independent bounded-deficit profile extractor reproduces A(16,5)=2306780 and A(18,6)=23078316. Its inputs use neither bf_k.c nor those answers. It still depends mathematically on the full face-profile enumeration formula.

The same method computes A(20,7)=199207020. Normalized R6 at held-out k=7 differs from the degree-five polynomial fitted on k=1..6 by 1/1001. Six points alone cannot refute a degree-five polynomial, and ugly coefficients are not a refutation. This seventh-point discrepancy is conditional on the face-profile expression; independent raw verification of A(20,7) is not claimed.

SageMath 10.10 actually executed the rational and 225-refinement assertions in CI run 40894795626, but the job failed serializing a Sage Integer to JSON after the assertions. The failure log is retained. Explicit int conversion fixes serialization; the observed Docker digest is now pinned for the rerun. Do not call the earlier job successful.

The plan, OpenAlex raw DOI response, access failures, historical literature targets and a complementary Claude repository handoff are preserved alongside these results. No direct Claude invocation is claimed.

The cumulant-support assembly and full enumeration remain open in Lean; the nonzero connected kernel is still the mathematical frontier.

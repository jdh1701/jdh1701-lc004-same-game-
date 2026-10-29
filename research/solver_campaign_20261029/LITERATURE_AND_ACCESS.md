# Literature and access ledger

Primary paper read: Franz Lehner, Free cumulants and enumeration of connected
partitions, arXiv math/0110030 (2001), European J. Combin. 23 (2002), 1025–1031,
DOI 10.1006/eujc.2002.0619. Original arXiv PDF inspected, especially Theorem 4.1.
Author publication list and journal metadata agree with the identification.

Its proof groups weighted partitions by their least noncrossing coarsening,
then uses multiplicativity and incidence inversion. This is directly relevant
prior art for our proposed connected-weight organization. The theorem's stated
weights are products of classical cumulants over blocks; our signed game
coefficients must first be proved multiplicative across NC regions. We cannot
identify these weight systems solely because both involve cumulants.

Actionable older primary references identified in its bibliography (not yet
read in this campaign):
- Touchard (1952), Sur un probleme de configurations et sur les fractions continues.
- Stein (1978), On a class of linked diagrams. I. Enumeration.
- Nijenhuis and Wilf (1979), The enumeration of connected graphs and linked diagrams.
- Beissinger (1985), The enumeration of irreducible combinatorial objects.
- Biane (1997), Some properties of crossings and partitions.
- Doubilet, Rota and Stanley (1972), On the foundations of combinatorial theory VI.
These are targeted sources for an actual kernel recurrence, not evidence of
newness or automatic proofs of our game-specific results.

OpenAlex exact DOI lookup succeeded (HTTP 200), work W2065089594, raw response
in access/openalex_lehner.json. Two broader requests returned 429. No rapid
retries; no negative bibliographic conclusion is drawn.

SageMath is not locally installed; apt has no sagemath candidate in this host.
Documented SageCell service and terms endpoints both returned HTTP 403. No
terms acceptance was sent. Therefore no remote Sage execution is claimed.
The CI workflow has a separate Sage job with exact rational-series and 225
partition-refinement controls. Its result must be inspected before reporting
Sage verification. Python controls are recorded separately.

There is no directly exposed Claude API here. HANDOFF_TO_CLAUDE.md is the
repository communication artifact. No response or execution by Claude is
claimed until its evidence is received.

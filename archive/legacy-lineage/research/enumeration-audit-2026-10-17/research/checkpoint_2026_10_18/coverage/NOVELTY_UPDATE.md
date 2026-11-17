# Originality boundary after the full-family proof

Date: 2026-10-18. The previous [novelty audit](../transport/NOVELTY_AUDIT.md)
remains the baseline. Existing numerical formulas, the solvability grammar,
generic inclusion-exclusion, and general partition-lattice machinery are
not claimed as new mathematics.

The candidate contribution now has a stronger precise form: for the signed
union coefficient of **all** noncrossing pair/triple witnesses, a partition
with an isolated four-position block has coefficient zero whenever another
block connects different cyclic gaps around those four positions.
`all_witness_four_block_zero` proves this for arbitrary board length, with
no witness-coverage or branch-classification assumption. The exact
statement and its proof boundary are in [STATUS.md](STATUS.md).

This removes the principal formal assumption in the previous candidate.
It does not by itself establish mathematical priority. The exact coefficient
family and gap condition should be compared with any alleged predecessor;
sharing the words noncrossing, cumulant or cancellation is insufficient
to establish either equivalence or originality.

## Additional source access

The cached preprint by Chris Burns and Benjamin Purcell,
[A note on Stephan's conjecture 77](https://oeis.org/A035615/a035615.pdf),
was read as extracted text across all six pages. It proves the binary
formula using rotations/complementation, an indexing transform and a
characterization of losing binary strings. Its circular-board argument
is prior art. The inspected preprint does not state the signed
partition-coefficient theorem above. This is a comparison with that
document, not a claim about the entire literature or every later version.
The earlier publisher-PDF extraction failure is preserved in the historical
audit; the cached preprint is the newly readable source.

Additional searches used the exact queries:

- `"same game" "noncrossing" partitions enumeration`
- `"Clickomania" "inclusion-exclusion"`
- `"same game" "cancellation" polynomials`

Results were mostly irrelevant game listings and unrelated uses of the
words. The useful primary result was the already known
[Biedl et al. Clickomania paper](https://erikdemaine.org/papers/ClickomaniaGameTheory2000/).
These searches have weak recall and do not materially establish originality.

## Research decision

Retain the theorem as a **Lean-verified structural result with unresolved
originality**. Develop the size-two and size-three consequences, full
component factorization and connected coefficients from this established
base. Do not extend known polynomial tables merely to label them novel,
and do not relabel formal infrastructure as a solution. A complete useful
enumeration method and an external originality assessment remain open.

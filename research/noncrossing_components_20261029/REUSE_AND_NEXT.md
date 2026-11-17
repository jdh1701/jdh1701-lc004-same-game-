# Reuse map and next formal targets

Do not reimplement the labeled-word signed-join theorem. It is already present
in the primary repository, research/LC004/2026-10-29-exact-audit/formal/LC004/
LabeledJoinEnumeration.lean (preserved at primary commit d49ac53d77b49dd12e01166663ed5f7b9c0ab6ed).
The source was reread during this session. It defines labeledWinningCount by
original RawMaxErases and proves labeledWinningCount_signed_joins, with the
constraint-coloring/quotient-function equivalence. It was not newly imported
or rebuilt in this checkpoint. Integrate its exact source with a combined
root audit when the weighted cumulant bridge is implemented.

Current new proof source: proof/noncrossing-components-20261029, 7c1c26ce.
The coefficient product is established for any noncrossing coarsening, not just
for words whose classes are all small. The closure pushforward theorem accepts
arbitrary signed weights and is logically separate from coefficient factoring.

Next concrete statements:
1. Restriction of p to a block of nc(p) has top NC closure.
2. The fiber {p | nc(p)=pi} is equivalent to the product of connected local
   partitions on pi's blocks; use the already checked regionPatternOrderIso.
3. Original color-class count equals the sum of local class counts under this
   equivalence. Hence b^(global count) factors as the product of local powers.
4. Weighted closure pushforward factors, giving the free moment-cumulant relation
   for labeledWinningCount. Distinguish the empty-moment convention from n>=1.
5. Nonzero collected coefficients are supported on certificate-generated joins;
   connect that support fact to R1/R2, then combine crossed-four cancellation.
6. Derive the universal n<5j support bound on those identified cumulants.
7. Find an effective new enumeration of the surviving connected coefficients.

Items 1-6 formalize the existing paper reduction; item 7 remains the genuinely
unresolved enumeration frontier. The current theorem does not supply item 7.
The five-block Fuss-Catalan proposal remains unproved and needs a decisive test.

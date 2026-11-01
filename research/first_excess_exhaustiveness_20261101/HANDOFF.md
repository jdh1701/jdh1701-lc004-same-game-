# Continuation after uniform first excess

The entire LC004/A035617 problem is still OPEN. This folder supplies a new
computer-assisted paper proof of UNIFORM first-excess exhaustiveness. Read
REPORT.md before using it; inspect receipts.json for the exact hosted status.
The full assembly is not Lean formalized.

The important new mechanism is exact elimination of one six-class via its
16-list, 2-Helly boundary family. Covered-majority cancellation is applied to
the projected outside family, NOT the original mixed 5-by-8 family, which is
known not to be majority closed. The Euler correction terms are coefficients
of actual (2,3)- or (2,4)-refined patterns and vanish separately by crossed-
small-class support. This forces exactly two outside assignments, then two
or three complete certificates. A four-gap switch handles the split-pair
three-certificate case; the simpler local shortcut is FALSE (FAILURES.md).

At the paper/exact-computation level the full first-excess totals are
22,312,5607,116857 at j=2,3,4,5, all coefficient -1. These are not A035617 terms.
No larger census is needed next. The next substantive target is higher excess
(one seven-class or two six-classes), testing exact boundary elimination,
Helly obstructions, and the actual Euler correction coefficients. Do not extend
the first-excess sign or family-size conclusions to those profiles: positive
coefficients are already known there.

Formalization obligations remain: actual 462-order-type geometry transport,
Euler decomposition and original refined-pattern identifications, projection
factorization and one-component proof, cyclic run assembly and four-gap switch.
SixBoundaryLists.lean proves local facts and the arbitrary-index Helly lemma,
not this whole chain. Preserve that distinction in status reports.

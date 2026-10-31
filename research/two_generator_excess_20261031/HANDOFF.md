# Exact remaining target after the core enumerations

The full LC004/A035617 problem is still OPEN. Do not report a completion
percentage or call either boundary-layer count an A035617 term.

## Established inputs

* PR46: restricted adjacent-triple cancellation is Lean-certified. Arbitrary
  position inflation preservation and the general five-class no-three-run
  theorem are paper proofs.
* PR47: ordinary and wraparound common-gap lemmas and local five-state facts
  are Lean-certified at464f98e0996dfea5e9c79bb98bccfb0daa03521b. Full build:
  247 modules,4164 audited declarations, both negative guards. The (1,2,2)
  all-five run-shape theorem and core/count assembly are paper proofs.
* All-five survivor counts through j7 are5,35,415,6455,118195,2413185. Every
  positive core has a separate complete original-family replay. The theorem
  H_j=2(5j+1)A_j/5 now counts the ENTIRE three-run first-excess layer uniformly.
* This folder enumerates the COMPLETE two-generator/full-join connected
  first-excess stratum, using the paper conditional extension of the five-class
  run theorem. Totals at j2..5:0,88,2121,49725. Exact verification pins are in
  receipts.json; no new Lean module is introduced.

## First-excess finishing obligation

Let p be NCConnected, have j>=2 classes with profile (6,5,...,5), and have
nonzero ORIGINAL signed-join coefficient. Assume its six-class has no run
of length three or more. Prove that its COMPLETE original certificate family
has exactly two members. Nonzero coefficient already forces their full join.

This is not proved. A pattern with three or more certificates, no three-run,
and nonzero coefficient has not been excluded uniformly. The complete n16
and n21 censuses give evidence; the current n26 search does not examine every
such potential counterexample.

If that obligation is proved, the two enumerated families exhaust first
excess, and the n26 total becomes116857. Until then116857 is only a lower
bound on the nonzero population, and -116857 is the known families' signed
contribution, not the proved full connected coefficient.

## Avoid repeating killed routes

* Connected proper all-five cores need not be survivors: a third original
  certificate exists in the retained PR47 counterexample. SCC is essential.
* In mixed profiles SCC is only a necessary filter in this algorithm.
  Complete original-family acceptance remains mandatory.
* The conditional five-class shape theorem assumes a COMPLETE two-generator
  full-join source. It cannot be used to establish that premise for all
  first-excess survivors.
* Survivor-only class deletion failed in the earlier n16/n21 censuses.
* Positive coefficients already occur beyond first excess, for example the
  earlier connected (5,7) and (5,8) cases. Do not extend the observed first-
  excess coefficient range to arbitrary higher excess.

The full higher-excess enumeration is a separate remaining obligation even
after the first-excess theorem. The current finite search is exponential;
no closed formula or tractable all-length complexity bound is established.

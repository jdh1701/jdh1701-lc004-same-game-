# Consolidated formal check of the 333-test research snapshot

V22–V25 extensions bring the explicit audit to 87 result theorems in 24
result modules, plus a separate verifier-control module. The original 333-test inventory remains historical,
not an automatically updated test count. The new lemmas prove pointwise XOR
row-operation equivalence, list lifting and existential satisfiability
preservation for arbitrary assignment types. They do not prove Python bitmask
correspondence, affine-basis completeness, unit propagation or solver runtime.
The V23 AffineProjection extension proves coordinate selection commutes with
Boolean-list XOR, projects generated choices, lifts projected witnesses, and
preserves satisfiability of predicates on the selected coordinates. It does not
prove independence, removal of redundant generators, Gaussian basis construction,
or the Python integer representation. Formal promotion requires a green replay.

Source: private Alexandria research commit d4fa2d79e9e7410bd35655c25ce69ccee6acd039.
All 333 Python tests were rerun successfully on 2026-09-27. They are not 333 proofs.
The inventory accounts for each test ID and source hash. 88 tests lie in mixed
mathematical/implementation suites; 245 concern software or empirical research
protocols. This file-level triage is not a claim of individual theorem coverage.

The proof-only export includes all 19 existing foundation modules and 63 explicit
theorems, including helper lemmas. It excludes the Alexandria engine. The runner
builds every module explicitly (including candidates omitted by the old default
root), audits each declaration at trustLevel 0, and requires no axioms or sorry.
A related Lean theorem does not prove the correctness of the Python program.
Finite certificate theorems establish their literal encoded CNFs; graph-generation
and Python/Lean correspondence require separate proofs.

Run `python consolidated/run.py` with elan/Lake installed. Lean is pinned to
4.34.0; neither formal project has external package dependencies. Source hashes
bind the initial bundle. The JSON report records per-module builds, per-theorem
results and failures. A green run verifies only the 87 inventoried result statements and requires
all five verifier controls to behave as expected.

## Missing formal obligations retained explicitly

- General circuit-to-CNF translation and its global size/witness correspondence:
  current gate truth tables are only local components.
- Python machine interpreter correspondence: current abstract machine lemmas
  do not establish correctness of serialization, interpreter or runtime tables.
- Concrete lower-width closure certificates for K4, prism, K3,3, linked K4,
  Q3 and M8; an unsatisfiability/refutation theorem alone gives no lower bound.
- General subsumption/weakening lifting and concrete instantiation of
  WidthClosedInvariant; its current theorem is conditional on an invariant.
- Triangle-free cubic graph theorem: local Boolean parity lemmas do not prove
  support-overlap classification, closure or the resulting graph-family bound.
- Exact expansion/cut profile calculations and grammar-depth rejection lemmas:
  Python evidence only in this bundle.
- Statistical or held-out performance/novelty claims: empirical validation is
  required; Lean cannot certify their real-world interpretation from test logs.
- Standard-model P-versus-NP bridge: none established by this export.

No exact minimum widths, new asymptotic lower bound, novelty, or P-versus-NP
solution is promoted by this workflow. Remaining software tests stay in Python.

## V24 mutual-span certificate scope

SpanReduction proves generator substitution, mutual-span equivalence,
dependent-generator deletion, zero deletion, and preservation of existential
predicates. Span is the inductive closure under a supplied zero and binary sum;
for XOR this is linear span. The coverage premises must actually be supplied.
Theorems do not establish the Python coefficient checker, Gaussian elimination,
independence, or equivalence with V23's one-use generator enumeration. New result
promotion requires the complete pinned replay; negative audit fixtures remain
excluded from mathematical result counts.

## V25 executable coefficient certificate scope

CoefficientChecker evaluates exact-length Boolean coefficient lists and proves
that accepted evaluations and rows belong to the input span. Mutually accepted
coverage certificates imply span equivalence and preserve existential predicates.
These five generic theorems impose no algebraic axioms on the binary operation;
they concern the inductive closure defined in SpanReduction.

CoefficientCertificateExample contains five finite/derived theorems exported
from the Python certificate for dimension 4, generators [3,5,6,8], support 7:
projected acceptance, full-space lift acceptance, corruption rejection, projected
span equivalence and lifted-span membership. This is one finite producer output,
not a proof that every Python output matches the Lean encoding. The separate
Python bounded audit checks 5,054 cases. Independence, integer/list correspondence,
one-use enumeration correspondence and full solver completeness remain open.

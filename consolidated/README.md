# Consolidated formal check of the 333-test research snapshot

V22 extension: five RowElimination declarations bring the explicit audit to
68 theorems in 20 modules. The original 333-test inventory remains historical,
not an automatically updated test count. The new lemmas prove pointwise XOR
row-operation equivalence, list lifting and existential satisfiability
preservation for arbitrary assignment types. They do not prove Python bitmask
correspondence, affine-basis completeness, unit propagation or solver runtime.

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
results and failures. A green run verifies only the 63 existing statements.

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

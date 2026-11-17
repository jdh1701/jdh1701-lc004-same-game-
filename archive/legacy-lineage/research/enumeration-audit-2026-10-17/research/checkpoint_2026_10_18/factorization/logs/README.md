# Execution provenance

- `lean_attempt1.log` through `lean_attempt3.log` are unsuccessful development
  builds. Their error-generated `sorryAx` output is not an accepted proof.
- `lean_attempt4.log` is the successful coefficient-factorization build.
- `geometry_attempt1.log` is an unsuccessful development build;
  `geometry_attempt2.log` is the successful final geometry/witness build.
- `axioms_verified.log` is the final signature/axiom audit of all 11 named
  theorems. All dependencies are standard Lean axioms; no proof holes remain.
- `source_audit.log` is the source scan, theorem inventory, and stage-count audit.
- `prediction14.log` records the conditional prediction before n=14 computation.
- `engine_checks.log` records exact Python/C++ coefficient-map comparisons
  through n=10, old polynomial controls through n=13, and the n=14 holdout.
- `quadratic_rival15.log` records the quadratic rival before n=15 computation.
- `raw_q3_n14.log` and `raw_q4_n14.log` record direct cell enumeration through
  n=14. `raw_q3_n15.log` extends the independent three-colour check through n=15.
- `inference15_from_raw.log` was created after the q=3 raw count but before
  the full n=15 witness-join result. It is explicitly conditional on degree <=3.
- `threshold15.log` records the full n=15 witness-join calculation.
- `raw_crosscheck.log` reports comparisons between partition polynomials and
  the direct raw-cell solver.

Predictions are within-session records, not externally preregistered claims.
The new C++ join engine shares its witness generator with the earlier Python
engine; the raw-cell enumerator shares neither witness nor join machinery.
The C++ programs are tested executables, not Lean-extracted certified code.
Signed additions and negations in the new join engine have overflow checks.

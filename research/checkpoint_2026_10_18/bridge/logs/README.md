# Literal execution records

- `bridge_attempt2.log`: successful final targeted Lean build. The new files
  were unchanged between this build and the axiom/source audits.
- `axioms_verified.log`: final signatures and axiom dependencies for all 12
  new named theorems.
- `progress_audit.log`: nine-stage count, theorem inventory, unchanged raw
  definition hashes, and source scan.
- `grammar_attempt1.log`, `grammar_attempt2.log`, `bridge_attempt1.log`:
  unsuccessful development attempts, retained as such; they are not evidence
  of accepted proofs.
- `cache.log`, `cache_takedrop.log`: dependency-cache acquisition output.
- `connected_weights.log`: complete n<=12 structural test and falsification
  output, including the rejected linear connected-weight model.
- `prediction_length13.log`: prediction recorded before the holdout run.
- `holdout_length13.log`: actual n=13 witness-join output and comparison.
- `raw_q3_n13.log`, `raw_q4_n13.log`: independent direct raw-cell enumeration.
- `raw_crosscheck.log`: 28 polynomial/raw count comparisons, all passing.
- `raw_q4_timing_failed.log`: `/usr/bin/time` was absent (exit 127), so this
  attempt did not execute the counter. It was rerun successfully with a Python
  subprocess timer, whose result is in `raw_q4_timing.log`.

Timing values are measurements of this host, not general complexity claims.
The full repository GitHub Actions run is separate from these local logs.

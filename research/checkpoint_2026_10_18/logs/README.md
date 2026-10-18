# Log interpretation

`lean_verified.log` and `axioms_verified.log` are the successful final
checks. `source_audit.log` corresponds to `../data/source_audit.json`.
`partition_counts.log` and `join_controls.log` are actual Python outputs.

Files named `first_attempt`, `second_attempt`, `third_attempt`, or
`crossing_attempt` preserve development output. The first two Lean attempts
and first crossing attempt failed; their error-generated placeholder axiom
reports are not evidence for the final sources. The third attempt and
crossing retry passed. No such placeholders remain in the final proofs.

Cache logs are operational evidence. Initial helper extraction failed
because archived ownership cannot be applied on this host. The already
downloaded helper was extracted without preserving ownership and installed
at the expected versioned filename. ProofWidgets release fetch was retried
successfully. The broad cache download was deliberately interrupted in
favour of targeted cache downloads, which completed. No dependency or
proof source was changed to bypass these setup failures.

# Alexandria research architecture after the LC004 geometric campaign

## Decision

Reuse the existing verification-first Core. This campaign required a mathematical construction and a reliable compiler environment; it did not justify a second architecture or a new autonomous-agent layer. Core code was not changed, and no comparative discovery speedup is claimed.

The inspected canonical integration snapshot is `fb413043cb0f4369615132e014691782a344af8a` on `integration/core-vnext-verification-20261029` in `jdh1701/Alexandria_Omega_New`.

Read components: `docs/ARCHITECTURE.md`, `alexandria_core/campaign.py`, `alexandria_core/models.py`, `tools/bounded_session.py`, `schemas/formal-proof-receipt.schema.json`, and the relevant verifier-router source. This is a task-directed inspection, not a renewed audit of the entire Core repository.

## Existing capabilities used and preserved

The campaign planner already provides a strict manifest, bounded task expansion, dependency order, stable identifiers, and a sealed planning receipt. The bounded-session runner binds cached analyses to scenario, source and runtime identities, records attempts, and distinguishes cached historical completion from fresh verification. The formal receipt schema requires exact claim, declaration, toolchain, source bundle, checker, kernel and auditor identities; the router reserves theorem promotion for an explicitly trusted authority.

The existing planner was executed unchanged on the six remaining LC004 obligations. Its two required source files were fetched from the frozen Core commit and hashed; no replacement implementation was written. Twenty-six planning executions were deterministic, and a mutation asserting a completed verification was rejected. These are planner-reproducibility checks, not proof production, model inference, or an equal-budget discovery experiment.

Artifacts:

* `research/alexandria_face_queue.json`: future-task manifest, single-task batches, concurrency one, six tasks, 1,800-second task limits and a 10,800-second aggregate ceiling.
* `research/alexandria_face_plan.json`: native Core plan with execution counters zero and `not_started` status.
* `research/alexandria_queue_receipt.json`: actual planner replay observations and source hashes.
* `scripts/replay_alexandria_face_queue.py`: replay against an existing frozen Core checkout.

The queue is not a scheduled automation. Completed Lean results are recorded in the separate proof ledger. No Core formal-authority receipt was issued: the campaign did not install or impersonate a trusted Core authority. Lean checking and Core receipt admission remain distinct.

## Changes supported by this campaign's evidence

| Observed issue | Applied change | Measurement or limit |
|---|---|---|
| Generic path lemmas left geometry assumed | Added actual rigid/heavy geometry and canonical carrier | Lean checks the substantive implication; no prose claim substitutes for it |
| Existing rigidity lemma required all classes small | Added local rigidity for one class | Supports mixed rigid/heavy patterns without strengthening the target hypothesis |
| Face modules were outside the normal root import closure | Added their imports to `LC004.lean` | Coverage/source guard sees all 159 active modules |
| Printed axiom lists were not an enforced gate in the baseline face workflow | Added `FaceAxiomAudit.lean` and a dedicated CI step | Final local audit checks 588 imported project declarations transitively |
| Finite tests examined unrestricted abstract partitions rather than the actual game | Added deletion/certificate/face comparisons and explicit mutations | 142,418 input patterns; exact finite scopes recorded |
| Full local build caused resource contention | Kept focused local compilation and used hosted full compilation | Local broad attempt interrupted; no throughput improvement asserted |
| Planning could be confused with execution | Used the existing native Core receipt unchanged | Zero executed/verified tasks in the future plan; mutation rejected |

These changes are in the LC004 proof and verification pipeline. They do not alter Core's theorem authority, evidence scoring, kernel or cache trust policy.

## Next architecture work, only after a discriminating benchmark

1. **Versioned claim-to-declaration intake.** Extend the existing Lean adapter's supported bundle handling to this Mathlib 4.19 project if needed; do not loosen the formal receipt schema. Freeze one true geometric theorem, one wrong statement mapping, one changed source, and one forbidden-axiom mutation. Require exact rejection of the three invalid cases and successful pinned replay of the valid one. Report artifact acquisition, compile time, audit time and trust configuration separately.

2. **Dependency-aware local compilation.** Compare the current target build with a candidate scheduler on the same cold cache and the same warm cache, with a fixed memory ceiling. Include dependency changes and failed compilations. Promote only if it reduces measured resources without reusing stale proofs. The interrupted broad build motivates this experiment but does not establish which scheduler is best.

3. **Research-result intake.** Attach the direct-deletion computation, certificate enumeration, face test and literature record as separately scoped evidence. Shared helper code and overlapping datasets must remain visible. Do not label agreement among implementations as statistical independence or as proof of novelty.

4. **Continuation executor.** If added later, consume the existing campaign manifest and emit a terminal receipt for every attempted task, with timeout and unresolved states preserved. It must not turn the planner's zero counters into successful theorem receipts. No model provider or background executor was added here.

5. **Literature availability.** Store exact source, access status, theorem number and the inference drawn from it. Kurz's failed PDF retrieval and the limits of the novelty search remain explicit. More search results alone cannot establish priority.

For each proposed capability, compare against the frozen Core with the same task inputs and resource budget. The current session supplies a reproducible baseline and a useful geometric theorem, not an architecture-performance claim. The next highest-value work is global certificate assembly, not an orchestration rewrite.

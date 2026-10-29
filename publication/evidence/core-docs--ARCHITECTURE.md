# Alexandria Core Architecture

## Design thesis

Alexandria is an epistemic compiler rather than an autonomous persona. Its input is a finite field
of claims, evidence, constraints, and a scrutiny policy. Its output is a reproducible decision
record that states what was selected, what was rejected, why, what remains unresolved, and what
would most efficiently reduce the remaining uncertainty.

The trusted core is deliberately small and local. Generative models may propose claims, evidence,
falsifiers, or proofs outside the kernel, but their output has no privileged status. It enters
through the same typed interfaces and gates as any other untrusted proposal.

## Execution pipeline

1. `Scenario.from_mapping` validates and canonicalizes claims and evidence.
2. `OmnisController` converts Lite, Research, or War mode into explicit gates.
3. `assess_protocol` verifies any preregistration seal and its binding to the scenario.
4. `VerifierRouter` runs every applicable deterministic or caller-registered verifier.
5. For a `theorem`, `formal_proof_gate` validates a receipt only from an explicitly trusted
   authority, binds it to the exact claim, reviewed formalization, proof bundle, and executing
   checker bundle, and fails closed otherwise.
6. `assess_claim` aggregates contextual evidence and applies blocking verifier results; evidence
   scores never discharge the theorem gate.
7. `TheoryEvolutionManager` compares dependency-complete, conflict-free subsets.
8. `SolomonAdversary` attacks the resulting claim field and emits falsification actions.
9. `ObligationEngine` compiles unresolved proof duties.
10. `EpistemicPressureMap` ranks the next valuable verification work.
11. `EvidenceLineageGraph` binds sources, claims, verifications, theories, attacks, and obligations.
12. `ReceiptLedger` commits the audit events and report core to a deterministic hash chain.

## Trust boundaries

| Boundary | Trusted guarantee | Explicitly not guaranteed |
|---|---|---|
| Typed input | Structural invariants and referential integrity | Truth of prose or authenticity of a URL |
| Local arithmetic | Restricted expression evaluated without dynamic execution | General theorem proving |
| Evidence hashes | The declared artifact can be content-addressed | The artifact is correct, independent, or honestly described |
| Protocol seal | Post-seal modification is detectable | The protocol is scientifically adequate |
| External verifier | Fixed execution bundle, bounded invocation, strict response contract | Network isolation in process mode or correctness of an unpinned binary |
| Theorem formalization | Exact native declaration and proof-bundle digest reviewed with the prose claim | Semantic adequacy of a human-approved formalization |
| Formal-proof authority | Explicit opt-in, claim/formalization/checker binding, closed goals and assumptions | Soundness of an authority, kernel, or auditor the caller chose to trust |
| Lean replay | Clean rebuild, source inventory, pinned toolchain, native kernel and transitive axiom audit | Proof of a theorem whose prose-to-formal mapping was never reviewed |
| Theory search | Dependency and conflict coherence under declared scores | Truth, causality, or calibrated probability |
| Receipts | Mutation of the retained report is detectable | Long-term identity without external signing or timestamping |
| Failure memory | Recurrence is retained transactionally | Automatic repair or safe self-modification |
| Campaign planning | Finite budgets, canonical task identities, dependency order, and a sealed non-execution receipt | Agent execution, statistical independence, truth, novelty, or theorem verification |

## Core invariants

- Claim and evidence identifiers are unique.
- Dependencies and conflicts reference known claims and cannot self-reference.
- Evidence weights and priors remain in `[0, 1]`.
- SHA-256 bindings use a canonical `sha256:<hex>` representation.
- Input order does not change the report.
- One independence group contributes at most its strongest item per direction.
- A selected theory is dependency-complete and conflict-free.
- A false arithmetic predicate cannot be selected.
- A theorem cannot be selected without a valid receipt from an explicitly trusted formal authority.
- The theorem receipt binds the full claim semantics, reviewed formal declaration, complete proof
  bundle, kernel, axiom auditor, and executing checker bundle, with no unresolved goals or
  assumptions.
- War mode fails closed on verifier errors and requires primary, hashed, preregistered evidence.
- Selected claims cannot retain blocking unsatisfied obligations.
- The lineage graph remains acyclic.
- Every report fingerprint, run identifier, final core receipt, and receipt predecessor is
  independently recomputable.
- Failure-memory insertion is idempotent for the same failure signature and run.

## External-verifier protocol

An adapter receives one UTF-8 JSON object on standard input and returns one UTF-8 JSON object on
standard output. The response schema requires `verdict`, `message`, and `details`. Any malformed
response becomes an error receipt. Fixed arguments are supplied by trusted configuration, never by
scenario prose. Requests include `formal_claim_digest`; theorem adapters return their proof receipt
under `details.formal_proof` and must be explicitly registered as formal-proof authorities. Such an
authority must pin the canonical execution-bundle digest covering its executable, literal arguments,
and absolute file arguments. The CLI accepts this operator trust configuration through a strict
verifier-registry document; scenarios cannot choose executables or grant proof authority to
themselves.

The Lean adapter additionally requires a theorem's `formalization` to identify `lean4`, the exact
declaration, and the canonical proof-bundle digest. It verifies every source hash and rejects
unlisted source, rebuilds in a fresh directory, checks the pinned Lean version, and asks a separately
hashed Lean executable to inspect transitive kernel axioms. `sorryAx` and undeclared axioms remain
unresolved assumptions and cannot generate a passing receipt.

War mode accepts an external adapter only when the caller declares container isolation and pins the
executable SHA-256 digest. This is a policy assertion that must be enforced by deployment tooling;
the Python process runner does not pretend to provide container or network isolation itself.
On POSIX systems, a dedicated isolated launcher applies resource limits before `exec`, avoiding the
thread-safety hazards of `preexec_fn`.

## Persistence model

Reports and receipt chains are immutable artifacts. SQLite failure memory is an index over failures,
not a source of truth. A repeated report cannot increment recurrence twice, while the same failure
in a distinct run increments its count. Source changes remain conventional reviewed Git commits;
failure memory never edits code.

## Campaign planning boundary

`alexandria_core.campaign` accepts a closed campaign manifest and expands it deterministically into
content-addressed task and batch identifiers. The workstream graph must be acyclic; task count,
batch width, nominal concurrency, per-task time, aggregate tokens, and aggregate wall time are
bounded. Every planning receipt reports `not_started`, zero execution counters, and
`planning_only_no_agents_invoked`.

The planner contains no model provider, queue, or verifier authority. Isolation-group labels are
provenance, not a claim of statistical independence. A future executor must produce terminal
results for every declared task and route any theorem artifact through the existing claim-bound
formal-proof gate; it may not derive truth from vote count or mutate the sealed plan.

## Extension rules

New components should either strengthen a named invariant or improve a preregistered benchmark.
They must not be accepted merely because they introduce another agent, loop, dashboard, score, or
symbolic label. Each extension needs:

1. a typed interface;
2. a declared trust boundary;
3. a failure behavior;
4. deterministic unit tests;
5. an adversarial test;
6. receipt-visible outputs; and
7. a benchmark hypothesis that can fail.

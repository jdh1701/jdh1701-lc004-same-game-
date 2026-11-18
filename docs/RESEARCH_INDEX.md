# Research index

Every research folder, grouped by line of attack. Paths are unchanged from the old repository so scripts, receipts and cross-references still resolve. "Source" is the old branch the folder was taken from; `docs/provenance.json` gives the exact commit and blob for every file.

Status words inside these folders follow the WORKBOARD vocabulary (PROVED-LEAN, PROVED-PAPER, VERIFIED-COMP, CONJECTURE, KILLED, RETRACTED). A folder's own REPORT/HANDOFF is the authority for its claims; this index certifies nothing.

## 1. Foundations: winning ⇔ noncrossing 2/3 certificate

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`lean_targets`](../research/lean_targets/) | 1 | — |  | `research/free-cumulants-20261029` |
| [`verification`](../research/verification/) | 18 | — |  | `review/claude-entropy-audit-20261112` |
| [`four_gap_verification`](../research/four_gap_verification/) | 5 | — |  | `review/claude-entropy-audit-20261112` |
| [`tool_grounded_20261029`](../research/tool_grounded_20261029/) | 17 | [`REPORT.md`](../research/tool_grounded_20261029/REPORT.md) | Tool-grounded continuation research | `verify/greedy-obstruction-20261029` |
| [`handoff_review_20261029`](../research/handoff_review_20261029/) | 29 | [`CONTINUATION_INDEX.md`](../research/handoff_review_20261029/CONTINUATION_INDEX.md) | Continuation index and archive completeness | `research/gpt-handoff-review-20261029` |
| [`physics_audit_20261029`](../research/physics_audit_20261029/) | 4 | [`REPORT.md`](../research/physics_audit_20261029/REPORT.md) | Physics, nature, economics and coding audit | `review/claude-entropy-audit-20261112` |

## 2. Counting by face decomposition, diagonals, free cumulants

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`face_decomposition`](../research/face_decomposition/) | 24 | [`NOTE.md`](../research/face_decomposition/NOTE.md) | Face decomposition for one-row Same Game patterns | `research/free-cumulants-20261029` |
| [`free_cumulants`](../research/free_cumulants/) | 32 | [`NOTE.md`](../research/free_cumulants/NOTE.md) | Free-cumulant reading of the winning-word counts (2026-10-29) | `research/free-cumulants-20261029` |
| [`overlap_20261029`](../research/overlap_20261029/) | 22 | [`REPORT.md`](../research/overlap_20261029/REPORT.md) | Certificate overlap and cancellation campaign | `review/claude-entropy-audit-20261112` |
| [`noncrossing_components_20261029`](../research/noncrossing_components_20261029/) | 19 | [`REPORT.md`](../research/noncrossing_components_20261029/REPORT.md) | Noncrossing coefficient decomposition checkpoint — 29 October 2026 | `research/gpt-handoff-review-20261029` |
| [`solver_campaign_20261029`](../research/solver_campaign_20261029/) | 33 | [`FIVE_BLOCK_HYPOTHESIS.md`](../research/solver_campaign_20261029/FIVE_BLOCK_HYPOTHESIS.md) | Focused unconventional lead: five-block kernel | `review/claude-entropy-audit-20261112` |
| [`class_count_20261029`](../research/class_count_20261029/) | 9 | [`REPORT.md`](../research/class_count_20261029/REPORT.md) | Class-count and weighted component checkpoint | `research/gpt-handoff-review-20261029` |
| [`weighted_fibers_20261029`](../research/weighted_fibers_20261029/) | 14 | [`REPORT.md`](../research/weighted_fibers_20261029/REPORT.md) | Original-game connected-weight expansion | `research/gpt-handoff-review-20261029` |
| [`closure_fibers_20261029`](../research/closure_fibers_20261029/) | 10 | [`REPORT.md`](../research/closure_fibers_20261029/REPORT.md) | Closure restriction checkpoint and method decision | `research/gpt-handoff-review-20261029` |
| [`connected_fiber_20261029`](../research/connected_fiber_20261029/) | 13 | [`REPORT.md`](../research/connected_fiber_20261029/REPORT.md) | Connected closure fiber checkpoint | `research/gpt-handoff-review-20261029` |
| [`fixed_content_333_20261117`](../research/fixed_content_333_20261117/) | 5 | [`REPORT.md`](../research/fixed_content_333_20261117/REPORT.md) | Fixed-content counts W(3,3,r): exact closed form; H1 binary polynomiality | `claude/fixed-content-333-20261117` |
| [`all_alphabets_20261118`](../research/all_alphabets_20261118/) | 3 | [`REPORT.md`](../research/all_alphabets_20261118/REPORT.md) | W_n(q) for every alphabet size, n ≤ 20, via the Lean cumulant degree bound | `claude/review-r20261104-20261118` |

## 3. All-five kernel and coefficient law

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`all_five_adversarial_20261029`](../research/all_five_adversarial_20261029/) | 9 | [`REPORT.md`](../research/all_five_adversarial_20261029/REPORT.md) | All-five adversarial search and projection formula | `review/claude-entropy-audit-20261112` |
| [`five_actual_20261029`](../research/five_actual_20261029/) | 37 | [`REPORT.md`](../research/five_actual_20261029/REPORT.md) | Actual five-class cancellation and an SCC survivor recognizer | `review/claude-entropy-audit-20261112` |
| [`five_bridge_20261029`](../research/five_bridge_20261029/) | 45 | [`REPORT.md`](../research/five_bridge_20261029/REPORT.md) | Original-game all-five coefficient bridge | `review/claude-entropy-audit-20261112` |
| [`five_geometry_20261029`](../research/five_geometry_20261029/) | 15 | [`REPORT.md`](../research/five_geometry_20261029/REPORT.md) | Five-class finite geometry bridge | `review/claude-entropy-audit-20261112` |
| [`five_kernel_20261029`](../research/five_kernel_20261029/) | 25 | [`REPORT.md`](../research/five_kernel_20261029/REPORT.md) | Kernel-checked five-versus-five geometry | `review/claude-entropy-audit-20261112` |
| [`scc_transfer_20261029`](../research/scc_transfer_20261029/) | 30 | [`REPORT.md`](../research/scc_transfer_20261029/REPORT.md) | Independent transfer/SCC enumeration: 415 and 6455 | `review/claude-entropy-audit-20261112` |
| [`choice_complex_20261029`](../research/choice_complex_20261029/) | 48 | [`REPORT.md`](../research/choice_complex_20261029/REPORT.md) | Choice-complex proof and baseline reconciliation, 2026-10-29 | `review/claude-entropy-audit-20261112` |
| [`choice_formalization_20261029`](../research/choice_formalization_20261029/) | 23 | [`REPORT.md`](../research/choice_formalization_20261029/REPORT.md) | Formal cancellation core, 2026-10-29 | `review/claude-entropy-audit-20261112` |
| [`choice_reduction_20261029`](../research/choice_reduction_20261029/) | 27 | [`REPORT.md`](../research/choice_reduction_20261029/REPORT.md) | Global coordinate reduction and abstract cancellation, 2026-10-29 | `review/claude-entropy-audit-20261112` |
| [`choice_support_20261029`](../research/choice_support_20261029/) | 17 | [`REPORT.md`](../research/choice_support_20261029/REPORT.md) | Support restriction and geometric cover criterion, 2026-10-29 | `review/claude-entropy-audit-20261112` |

## 4. Mixed kernels, separators, finishing attacks

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`mixed_kernel_20261030`](../research/mixed_kernel_20261030/) | 17 | [`REPORT.md`](../research/mixed_kernel_20261030/REPORT.md) | Original mixed (5,6) kernel: verified obstruction and local transfer | `review/claude-entropy-audit-20261112` |
| [`ten_attacks_20261030`](../research/ten_attacks_20261030/) | 15 | [`REPORT.md`](../research/ten_attacks_20261030/REPORT.md) | Ten attacks on exact Same Game enumeration | `review/claude-entropy-audit-20261112` |
| [`separator_collapse_20261030`](../research/separator_collapse_20261030/) | 21 | [`REPORT.md`](../research/separator_collapse_20261030/REPORT.md) | Sparse rescue of separator budget skips and independent collapse census | `research/separator-collapse-census-20261030` |
| [`fiber_elimination_20261030`](../research/fiber_elimination_20261030/) | 14 | [`REPORT.md`](../research/fiber_elimination_20261030/REPORT.md) | Classwise separators and five-row elimination | `review/claude-entropy-audit-20261112` |
| [`finishing_routes_20261030`](../research/finishing_routes_20261030/) | 19 | [`REPORT.md`](../research/finishing_routes_20261030/REPORT.md) | Ten further finishing attempts: connected support and the remaining obstruction | `review/claude-entropy-audit-20261112` |
| [`connected_support_20261030`](../research/connected_support_20261030/) | 4 | — |  | `review/claude-entropy-audit-20261112` |

## 5. First-excess layer and seven-class work

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`first_excess_20261030`](../research/first_excess_20261030/) | 26 | [`REPORT.md`](../research/first_excess_20261030/REPORT.md) | First excess: a uniform profile theorem and the complete (5,5,6) census | `review/claude-entropy-audit-20261112` |
| [`first_excess_20261031`](../research/first_excess_20261031/) | 18 | [`REPORT.md`](../research/first_excess_20261031/REPORT.md) | First-excess n21: complete census and a failed recursive reduction | `review/claude-entropy-audit-20261112` |
| [`inflation_law_20261031`](../research/inflation_law_20261031/) | 14 | [`REPORT.md`](../research/inflation_law_20261031/REPORT.md) | Adjacent inflation: an exact local rule and a sign obstruction | `review/claude-entropy-audit-20261112` |
| [`adjacent_contraction_20261031`](../research/adjacent_contraction_20261031/) | 8 | [`REPORT.md`](../research/adjacent_contraction_20261031/REPORT.md) | Adjacent contraction closes the restricted cancellation gap | `review/claude-entropy-audit-20261112` |
| [`primitive_core_20261031`](../research/primitive_core_20261031/) | 15 | [`REPORT.md`](../research/primitive_core_20261031/REPORT.md) | Common certificate gaps and the all-five primitive core | `review/claude-entropy-audit-20261112` |
| [`two_generator_excess_20261031`](../research/two_generator_excess_20261031/) | 19 | [`REPORT.md`](../research/two_generator_excess_20261031/REPORT.md) | Complete two-generator first-excess enumeration | `review/claude-entropy-audit-20261112` |
| [`first_excess_exhaustiveness_20261101`](../research/first_excess_exhaustiveness_20261101/) | 8 | [`REPORT.md`](../research/first_excess_exhaustiveness_20261101/REPORT.md) | Uniform first-excess exhaustiveness | `review/claude-entropy-audit-20261112` |
| [`seven_boundary_20261101`](../research/seven_boundary_20261101/) | 6 | [`REPORT.md`](../research/seven_boundary_20261101/REPORT.md) | Beyond first excess: a seven-class has exact ternary elimination | `review/claude-entropy-audit-20261112` |
| [`seven_pair_deletion_20261101`](../research/seven_pair_deletion_20261101/) | 7 | [`REPORT.md`](../research/seven_pair_deletion_20261101/REPORT.md) | Seven-class deletion and an iterated coefficient multiplier | `review/claude-entropy-audit-20261112` |

## 6. Fusion automaton, exact counts to n=28, growth rate

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`global_fusion_20261101`](../research/global_fusion_20261101/) | 20 | [`REPORT.md`](../research/global_fusion_20261101/REPORT.md) | Global Boolean fusion route (2026-11-01) | `review/claude-entropy-audit-20261112` |
| [`fusion_horizon_20261101`](../research/fusion_horizon_20261101/) | 13 | [`REPORT.md`](../research/fusion_horizon_20261101/REPORT.md) | Finite horizons and reversal-averaged enumeration | `review/claude-entropy-audit-20261112` |
| [`entropy_certificate_20261111`](../research/entropy_certificate_20261111/) | 12 | [`REPORT.md`](../research/entropy_certificate_20261111/REPORT.md) | LC004: a certificate-based ternary growth lower bound | `review/claude-entropy-audit-20261112` |
| [`extra_color_state_20261117`](../research/extra_color_state_20261117/) | 10 | [`REPORT.md`](../research/extra_color_state_20261117/REPORT.md) | Extra-base-color refinement: a certified finite-model comparison | `research/extra-color-state-20261117` |

## 7. Cross-domain, exploration, reviews, coordination

| Folder | Files | Entry point | Headline | Source branch |
|---|---|---|---|---|
| [`cross_domain_20261029`](../research/cross_domain_20261029/) | 13 | [`RESEARCH.md`](../research/cross_domain_20261029/RESEARCH.md) | Cross-domain campaign: RNA topology, parsing, and information loss | `review/claude-entropy-audit-20261112` |
| [`claude_exploration_20261029`](../research/claude_exploration_20261029/) | 5 | [`REPORT.md`](../research/claude_exploration_20261029/REPORT.md) | Open-ended Python exploration environment (Claude, own initiative) | `exploration/claude-sage-20261029` |
| [`claude_review_20261029`](../research/claude_review_20261029/) | 4 | [`CLAUDE_HANDOFF_2_SNAPSHOT.md`](../research/claude_review_20261029/CLAUDE_HANDOFF_2_SNAPSHOT.md) | Claude -> GPT handoff 2 (2026-10-29 ~16:00). Branch research/free-cumulants-20261029, PR #31. | `review/claude-entropy-audit-20261112` |
| [`coordination`](../research/coordination/) | 3 | [`README.md`](../research/coordination/README.md) | LC004 shared ChatGPT ↔ Claude coordination | `review/claude-entropy-audit-20261112` |
| [`archive`](../research/archive/) | 6 | — |  | `review/claude-entropy-audit-20261112` |

## 0. Loose files in `research/` (Oct 28 foundation era)

94 files: dated notes and their checker scripts from the work that produced the main Lean theorem chain. Key ones:

- [`WORKBOARD.md`](../research/WORKBOARD.md): the canonical claim registry and session log. Start here for any claim.
- [`UNIQUE_PATH_THEOREM_JOURNAL_DRAFT.md`](../research/UNIQUE_PATH_THEOREM_JOURNAL_DRAFT.md): journal draft of the uniqueness theorem.
- [`REVIEW_CORRECTIONS_2026_10_28.md`](../research/REVIEW_CORRECTIONS_2026_10_28.md) and [`REPOSITORY_WIDE_CORRECTION_AND_CLAUDE_HANDOFF_20261104.md`](../research/REPOSITORY_WIDE_CORRECTION_AND_CLAUDE_HANDOFF_20261104.md): corrections and retractions.
- `*_CI_RECEIPTS_*.json`: pinned CI run evidence.

<details><summary>Full list</summary>

- [`CANONICAL_PARSE_CYCLE_2026_10_28.md`](../research/CANONICAL_PARSE_CYCLE_2026_10_28.md)
- [`CERTIFICATE_JOIN_ENUMERATION.md`](../research/CERTIFICATE_JOIN_ENUMERATION.md)
- [`CONTEXTUAL_WIN_INSERTION_2026_10_28.md`](../research/CONTEXTUAL_WIN_INSERTION_2026_10_28.md)
- [`ContinuationSummaryObstruction.lean`](../research/ContinuationSummaryObstruction.lean)
- [`DIRECT_GRAMMAR_DETERMINIZATION_2026_10_28.md`](../research/DIRECT_GRAMMAR_DETERMINIZATION_2026_10_28.md)
- [`FACE_DECOMPOSITION_ADVERSARIAL_AUDIT_2026_10_28.md`](../research/FACE_DECOMPOSITION_ADVERSARIAL_AUDIT_2026_10_28.md)
- [`FIVE_ACTUAL_CI_RECEIPTS_20261029.json`](../research/FIVE_ACTUAL_CI_RECEIPTS_20261029.json)
- [`FIVE_ACTUAL_LITERATURE_20261029.md`](../research/FIVE_ACTUAL_LITERATURE_20261029.md)
- [`FIVE_BRIDGE_CI_EXACT_20261029.log`](../research/FIVE_BRIDGE_CI_EXACT_20261029.log)
- [`FIVE_BRIDGE_CI_LEAN_20261029.log`](../research/FIVE_BRIDGE_CI_LEAN_20261029.log)
- [`FIVE_BRIDGE_CI_RECEIPTS_20261029.json`](../research/FIVE_BRIDGE_CI_RECEIPTS_20261029.json)
- [`FIVE_BRIDGE_CI_SAGE_20261029.log`](../research/FIVE_BRIDGE_CI_SAGE_20261029.log)
- [`FIVE_KERNEL_CI_RECEIPTS_20261029.json`](../research/FIVE_KERNEL_CI_RECEIPTS_20261029.json)
- [`FOUR_GAP_LEAN_CHECKPOINT_20261029.md`](../research/FOUR_GAP_LEAN_CHECKPOINT_20261029.md)
- [`GRAMMAR_APPEND_2026_10_28.md`](../research/GRAMMAR_APPEND_2026_10_28.md)
- [`GRAMMAR_DERIVATION_COUNT_2026_10_28.md`](../research/GRAMMAR_DERIVATION_COUNT_2026_10_28.md)
- [`GRAMMAR_ERASE_SOUNDNESS_2026_10_28.md`](../research/GRAMMAR_ERASE_SOUNDNESS_2026_10_28.md)
- [`HANDOFF_TO_GPT_20261029.md`](../research/HANDOFF_TO_GPT_20261029.md)
- [`HANDOFF_TO_GPT_2_20261029.md`](../research/HANDOFF_TO_GPT_2_20261029.md)
- [`HeavyGreedyObstruction.lean`](../research/HeavyGreedyObstruction.lean)
- [`IDEAS_FOR_GPT_20261029.md`](../research/IDEAS_FOR_GPT_20261029.md)
- [`INDEXED_NONCROSSING_FOUNDATION_2026_10_28.md`](../research/INDEXED_NONCROSSING_FOUNDATION_2026_10_28.md)
- [`INSERTION_CLOSURE_2026_10_28.md`](../research/INSERTION_CLOSURE_2026_10_28.md)
- [`INSERTION_NAIVE_COUNTEREXAMPLE_2026_10_28.md`](../research/INSERTION_NAIVE_COUNTEREXAMPLE_2026_10_28.md)
- [`INSERTION_THREE_CASE_PROOF_2026_10_28.md`](../research/INSERTION_THREE_CASE_PROOF_2026_10_28.md)
- [`LEAN_CI_AUDIT_2026_10_28.md`](../research/LEAN_CI_AUDIT_2026_10_28.md)
- [`MAXRUN_REFINEMENT_2026_10_28.md`](../research/MAXRUN_REFINEMENT_2026_10_28.md)
- [`MIXED_KERNEL_CI_RECEIPTS_20261030.json`](../research/MIXED_KERNEL_CI_RECEIPTS_20261030.json)
- [`NEGATIVE_RESULTS.md`](../research/NEGATIVE_RESULTS.md)
- [`NONCROSSING_BLOCK_FAMILY_2026_10_28.md`](../research/NONCROSSING_BLOCK_FAMILY_2026_10_28.md)
- [`ORBIT_GRAMMAR_DFA_2026_10_28.md`](../research/ORBIT_GRAMMAR_DFA_2026_10_28.md)
- [`ORBIT_N16_AND_N17_TIMEOUT_2026_10_28.md`](../research/ORBIT_N16_AND_N17_TIMEOUT_2026_10_28.md)
- [`OVERLAP_CRITERION_2026_10_28.md`](../research/OVERLAP_CRITERION_2026_10_28.md)
- [`PAIR_TRIPLE_LIFT_2026_10_28.md`](../research/PAIR_TRIPLE_LIFT_2026_10_28.md)
- [`REPOSITORY_WIDE_CORRECTION_AND_CLAUDE_HANDOFF_20261104.md`](../research/REPOSITORY_WIDE_CORRECTION_AND_CLAUDE_HANDOFF_20261104.md)
- [`RESIDUAL_AUTOMATA_2026_10_28.md`](../research/RESIDUAL_AUTOMATA_2026_10_28.md)
- [`REVERSE_INSERTION_HISTORY_CERTIFICATE_2026_10_28.md`](../research/REVERSE_INSERTION_HISTORY_CERTIFICATE_2026_10_28.md)
- [`REVIEW_CORRECTIONS_2026_10_28.md`](../research/REVIEW_CORRECTIONS_2026_10_28.md)
- [`SCC_TRANSFER_CI_JOB_20261029.log`](../research/SCC_TRANSFER_CI_JOB_20261029.log)
- [`SCC_TRANSFER_CI_RECEIPTS_20261029.json`](../research/SCC_TRANSFER_CI_RECEIPTS_20261029.json)
- [`SCC_TRANSFER_HANDOFF_TO_CLAUDE_20261029.md`](../research/SCC_TRANSFER_HANDOFF_TO_CLAUDE_20261029.md)
- [`SECOND_DIAGONAL_BIJECTION_PROOF_2026_10_28.md`](../research/SECOND_DIAGONAL_BIJECTION_PROOF_2026_10_28.md)
- [`SECOND_DIAGONAL_FORMULA_2026_10_28.md`](../research/SECOND_DIAGONAL_FORMULA_2026_10_28.md)
- [`SECOND_DIAGONAL_PAPER_PROOF_2026_10_28.md`](../research/SECOND_DIAGONAL_PAPER_PROOF_2026_10_28.md)
- [`STRATEGY_RESET_2026_10_28.md`](../research/STRATEGY_RESET_2026_10_28.md)
- [`SYMBOLIC_RGS_COUNT_2026_10_28.md`](../research/SYMBOLIC_RGS_COUNT_2026_10_28.md)
- [`TERNARY_RECURRENCE_HOLDOUT_2026_10_28.md`](../research/TERNARY_RECURRENCE_HOLDOUT_2026_10_28.md)
- [`UNIQUE_PATH_THEOREM_JOURNAL_DRAFT.md`](../research/UNIQUE_PATH_THEOREM_JOURNAL_DRAFT.md)
- [`WORKBOARD.md`](../research/WORKBOARD.md)
- [`alexandria_face_plan.json`](../research/alexandria_face_plan.json)
- [`alexandria_face_queue.json`](../research/alexandria_face_queue.json)
- [`alexandria_face_queue_progress.json`](../research/alexandria_face_queue_progress.json)
- [`alexandria_face_remaining_plan.json`](../research/alexandria_face_remaining_plan.json)
- [`alexandria_face_remaining_plan_receipt.json`](../research/alexandria_face_remaining_plan_receipt.json)
- [`alexandria_face_remaining_queue.json`](../research/alexandria_face_remaining_queue.json)
- [`alexandria_queue_receipt.json`](../research/alexandria_queue_receipt.json)
- [`canonical_parse_cycle_2026_10_28.py`](../research/canonical_parse_cycle_2026_10_28.py)
- [`certificate_join_count.py`](../research/certificate_join_count.py)
- [`check_partition_degree_encoding.py`](../research/check_partition_degree_encoding.py)
- [`check_rgs_symbolic_count.py`](../research/check_rgs_symbolic_count.py)
- [`contextual_win_insertion_2026_10_28.py`](../research/contextual_win_insertion_2026_10_28.py)
- [`direct_grammar_dfa.py`](../research/direct_grammar_dfa.py)
- [`exhaustive_structure.py`](../research/exhaustive_structure.py)
- [`face_decomposition_counterexamples.json`](../research/face_decomposition_counterexamples.json)
- [`face_decomposition_dependency_graph.json`](../research/face_decomposition_dependency_graph.json)
- [`face_decomposition_proof_ledger.json`](../research/face_decomposition_proof_ledger.json)
- [`face_decomposition_verification.json`](../research/face_decomposition_verification.json)
- [`face_path_exhaustive.py`](../research/face_path_exhaustive.py)
- [`face_path_locality_check.py`](../research/face_path_locality_check.py)
- [`heavy_face_assembly_check.py`](../research/heavy_face_assembly_check.py)
- [`heavy_face_assembly_results.json`](../research/heavy_face_assembly_results.json)
- [`heavy_face_counterexamples.json`](../research/heavy_face_counterexamples.json)
- [`heavy_face_proof_ledger.json`](../research/heavy_face_proof_ledger.json)
- [`heavy_face_verification.json`](../research/heavy_face_verification.json)
- [`heavy_greedy_lean_audit.log`](../research/heavy_greedy_lean_audit.log)
- [`heavy_greedy_obstruction.py`](../research/heavy_greedy_obstruction.py)
- [`heavy_greedy_obstruction_report.md`](../research/heavy_greedy_obstruction_report.md)
- [`heavy_greedy_obstruction_results.json`](../research/heavy_greedy_obstruction_results.json)
- [`heavy_greedy_verification.json`](../research/heavy_greedy_verification.json)
- [`insertion_naive_counterexample_2026_10_28.py`](../research/insertion_naive_counterexample_2026_10_28.py)
- [`orbit_grammar_dfa.py`](../research/orbit_grammar_dfa.py)
- [`overlap_criterion_test.py`](../research/overlap_criterion_test.py)
- [`residual_automata_2026_10_28.py`](../research/residual_automata_2026_10_28.py)
- [`rgs_symbolic_count.py`](../research/rgs_symbolic_count.py)
- [`rigid_face_dependency_graph.json`](../research/rigid_face_dependency_graph.json)
- [`rigid_face_geometry_check.py`](../research/rigid_face_geometry_check.py)
- [`rigid_face_geometry_results.json`](../research/rigid_face_geometry_results.json)
- [`same_game_bridge_test_2026_10_28.py`](../research/same_game_bridge_test_2026_10_28.py)
- [`same_game_insertion_cycle.py`](../research/same_game_insertion_cycle.py)
- [`same_game_run_refinement_2026_10_28.py`](../research/same_game_run_refinement_2026_10_28.py)
- [`second_diagonal_formula_check.py`](../research/second_diagonal_formula_check.py)
- [`second_diagonal_independent_n16.py`](../research/second_diagonal_independent_n16.py)
- [`ternary_recurrence_holdout_2026_10_28.py`](../research/ternary_recurrence_holdout_2026_10_28.py)
- [`validate_direct_grammar_dfa.py`](../research/validate_direct_grammar_dfa.py)

</details>

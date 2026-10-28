import LC004.EncodingAgreement
import LC004.RawMaxSemanticsBridge
import LC004.RawIsolatedInsertion
import LC004.RawAnywhereHeaviness
import LC004.RawAnywhereRepeat
import LC004.GrammarErase
import LC004.ConditionalGrammarBridge
import LC004.ConditionalInsertion

/-!
This is a reproducible Lean compiler audit, not a statement of publication
novelty. The CI log records the exact axioms used by each selected theorem.
An explicit conditional theorem remains conditional regardless of the axioms
reported by #print axioms.
-/

#print axioms LC004.encode_eq_encodeRuns
#print axioms LC004.grammar_erases_empty
#print axioms LC004.raw_max_path_to_erases
#print axioms LC004.isolated_block_preserves_raw_win
#print axioms LC004.encode_duplicate_anywhere_heavier
#print axioms LC004.encoded_duplicate_anywhere_solvable
#print axioms LC004.encoded_repeat_anywhere_solvable
#print axioms LC004.grammar_implies_win_of_one_step_lift
#print axioms LC004.win_insert_grammar_of_lift

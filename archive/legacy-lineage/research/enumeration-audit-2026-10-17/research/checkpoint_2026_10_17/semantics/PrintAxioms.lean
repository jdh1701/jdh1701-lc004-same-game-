import LC004

#print LC004.ordinaryStepAt_map_encode
#print LC004.ordinary_unique_first_iff_path
#print LC004.ordinary_unique_path_eq_medianPath
#print axioms LC004.ordinaryStepAtFuel_map_encode
#print axioms LC004.ordinaryStepAt_map_encode
#print axioms LC004.encode_expandRuns
#print axioms LC004.ordinary_expansion_path_iff
#print axioms LC004.ordinary_path_iff
#print axioms LC004.ordinary_solvable_iff
#print axioms LC004.ordinary_unique_first_iff_path
#print axioms LC004.ordinary_unique_path_eq_medianPath
#print axioms LC004.ordinary_unique_path_color_palindrome
#print axioms LC004.mem_ordinarySolutionPaths_iff
#print axioms LC004.ordinary_paths_invariant_of_encode_eq
#print axioms LC004.ordinary_path_count_invariant_of_encode_eq
#print axioms LC004.stepAt_heavier
#print axioms LC004.successfulPath_heavier
#print axioms LC004.solutionPaths_card_mono
#print axioms LC004.ambiguity_heavier
#print axioms LC004.uniqueSuccessfulPath_of_heavier
#print LC004.sixWay_all_proper_unique
#print LC004.fiveWay_all_proper_unique
#print axioms LC004.sixWay_maximal_proper_cards
#print axioms LC004.sixWay_all_proper_unique
#print axioms LC004.sixWay_full_not_unique
#print axioms LC004.fiveWay_maximal_proper_cards
#print axioms LC004.fiveWay_all_proper_unique
#print axioms LC004.fiveWay_full_not_unique
#print axioms LC004.sixWay_raw_proper_unique
#print axioms LC004.sixWay_raw_full_not_unique
#print axioms LC004.fiveWay_raw_proper_unique
#print axioms LC004.fiveWay_raw_full_not_unique

-- Exact raw successors still cannot be recovered from the Boolean quotient.
example : LC004.ordinaryStepAt [0,0,1,1] 0 = some [1,1] := by rfl
example : LC004.ordinaryStepAt [0,0,1,1] 0 ≠ some [1,1,1] := by decide
example : LC004.encode [1,1] = LC004.encode [1,1,1] := by rfl

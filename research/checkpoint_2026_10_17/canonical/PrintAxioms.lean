import LC004

#print LC004.unique_successful_path_eq_medianPath
#print LC004.unique_successful_path_length
#print LC004.unique_successful_path_medianPath_success
#print axioms LC004.unique_successful_path_eq_medianPath
#print axioms LC004.unique_successful_path_length
#print axioms LC004.unique_successful_path_medianPath_success
#print axioms LC004.medianPath_failure_excludes_unique
#print LC004.mem_solutionPaths_iff
#print LC004.uniqueSuccessfulPath_iff_card_solutionPaths
#print axioms LC004.mem_pathSetFuel
#print axioms LC004.mem_solutionPaths_iff
#print axioms LC004.uniqueSuccessfulPath_iff_card_solutionPaths
#print axioms LC004.fourWay_proper_mask_cards
#print axioms LC004.fourWay_all_proper_unique
#print axioms LC004.fourWay_full_mask_card
#print axioms LC004.fourWay_full_mask_not_unique
#print axioms LC004.fourWay_only_short_path

example : LC004.medianPath 7 = [3,2,1,0] := by rfl
example : LC004.medianPath 0 = [] := by rfl

-- Negative control: the candidate succeeds but is not the only solution.
example : LC004.SuccessfulPath
    [(0,false),(1,false),(0,true),(1,true),(0,false),(1,true),(0,false)]
    [3,2,1,0] := by rfl
example : LC004.SuccessfulPath
    [(0,false),(1,false),(0,true),(1,true),(0,false),(1,true),(0,false)]
    [2,1,1,0] := by rfl

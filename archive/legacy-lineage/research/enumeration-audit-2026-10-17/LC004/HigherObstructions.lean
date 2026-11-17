import LC004.PathMonotonicity
import LC004.OrdinaryFinal

namespace LC004

/-- Six optional heavies on a fixed three-colour palindrome. -/
def sixWayState (mask : Nat) : RunState :=
  [(0,false), (1,mask.testBit 0), (0,false), (2,mask.testBit 1),
   (1,false), (2,false), (0,mask.testBit 2), (1,false), (0,true),
   (1,mask.testBit 3), (0,false), (2,mask.testBit 4), (1,false),
   (2,false), (0,mask.testBit 5), (1,false), (0,false)]

theorem sixWay_normalized (mask : Nat) : Normalized (sixWayState mask) := by
  simp [sixWayState, Normalized]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem sixWay_maximal_proper_cards :
    ∀ i : Fin 6, (solutionPaths (sixWayState (63 - 2^i.val))).card = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem sixWay_proper_heavier :
    ∀ mask : Fin 63, ∃ i : Fin 6,
      Heavier (sixWayState mask.val) (sixWayState (63 - 2^i.val)) := by
  simp only [sixWayState, Heavier, true_and, true_implies, false_implies,
    Bool.false_eq_true]
  decide

theorem sixWay_canonical_success :
    ∀ mask : Fin 64, SuccessfulPath (sixWayState mask.val) [8,7,6,5,4,3,2,1,0] := by
  unfold SuccessfulPath
  decide

/-- Every one of the 63 proper subsets has exactly one complete path.
Only six maximal subsets require tree evaluation; the rest follow by the
proved index-preserving monotonicity theorem and the canonical witness. -/
theorem sixWay_all_proper_unique (mask : Fin 63) :
    UniqueSuccessfulPath (sixWayState mask.val) := by
  obtain ⟨i,hi⟩ := sixWay_proper_heavier mask
  apply uniqueSuccessfulPath_of_heavier hi
  · exact (uniqueSuccessfulPath_iff_card_solutionPaths _).mpr
      (sixWay_maximal_proper_cards i)
  · exact sixWay_canonical_success ⟨mask.val, by omega⟩

theorem sixWay_full_not_unique : ¬ UniqueSuccessfulPath (sixWayState 63) := by
  rintro ⟨p,hp,huniq⟩
  have h1 := huniq [8,7,6,5,4,3,2,1,0] (by rfl)
  have h2 := huniq [1,1,3,5,4,4,3,2,2,1,0] (by rfl)
  have he := h1.trans h2.symm
  contradiction

#print axioms sixWay_all_proper_unique
#print axioms sixWay_full_not_unique

/-- An odd-cardinality obstruction on another three-colour palindrome. -/
def fiveWayState (mask : Nat) : RunState :=
  [(0,false), (1,false), (2,mask.testBit 0), (0,mask.testBit 1),
   (1,false), (0,false), (1,false), (0,mask.testBit 2), (2,true),
   (0,false), (1,mask.testBit 3), (0,false), (1,mask.testBit 4),
   (0,false), (2,false), (1,false), (0,false)]

theorem fiveWay_normalized (mask : Nat) : Normalized (fiveWayState mask) := by
  simp [fiveWayState, Normalized]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem fiveWay_maximal_proper_cards :
    ∀ i : Fin 5, (solutionPaths (fiveWayState (31 - 2^i.val))).card = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem fiveWay_proper_heavier :
    ∀ mask : Fin 31, ∃ i : Fin 5,
      Heavier (fiveWayState mask.val) (fiveWayState (31 - 2^i.val)) := by
  simp only [fiveWayState, Heavier, true_and, true_implies, false_implies,
    Bool.false_eq_true]
  decide

theorem fiveWay_canonical_success :
    ∀ mask : Fin 32, SuccessfulPath (fiveWayState mask.val) [8,7,6,5,4,3,2,1,0] := by
  unfold SuccessfulPath
  decide

theorem fiveWay_all_proper_unique (mask : Fin 31) :
    UniqueSuccessfulPath (fiveWayState mask.val) := by
  obtain ⟨i,hi⟩ := fiveWay_proper_heavier mask
  apply uniqueSuccessfulPath_of_heavier hi
  · exact (uniqueSuccessfulPath_iff_card_solutionPaths _).mpr
      (fiveWay_maximal_proper_cards i)
  · exact fiveWay_canonical_success ⟨mask.val, by omega⟩

theorem fiveWay_full_not_unique : ¬ UniqueSuccessfulPath (fiveWayState 31) := by
  rintro ⟨p,hp,huniq⟩
  have h1 := huniq [8,7,6,5,4,3,2,1,0] (by rfl)
  have h2 := huniq [2,2,1,2,4,4,3,2,1,0] (by rfl)
  have he := h1.trans h2.symm
  contradiction

#print axioms fiveWay_all_proper_unique
#print axioms fiveWay_full_not_unique

theorem sixWay_raw_proper_unique (mask : Fin 63) :
    OrdinaryUniqueSuccessfulPath ordinaryStepAt (expandRuns (sixWayState mask.val)) := by
  apply (ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode _).mpr
  rw [encode_expandRuns (sixWay_normalized _)]
  exact sixWay_all_proper_unique mask

theorem sixWay_raw_full_not_unique :
    ¬ OrdinaryUniqueSuccessfulPath ordinaryStepAt (expandRuns (sixWayState 63)) := by
  intro hu
  apply sixWay_full_not_unique
  have h := (ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode _).mp hu
  simpa only [encode_expandRuns (sixWay_normalized 63)] using h

theorem fiveWay_raw_proper_unique (mask : Fin 31) :
    OrdinaryUniqueSuccessfulPath ordinaryStepAt (expandRuns (fiveWayState mask.val)) := by
  apply (ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode _).mpr
  rw [encode_expandRuns (fiveWay_normalized _)]
  exact fiveWay_all_proper_unique mask

theorem fiveWay_raw_full_not_unique :
    ¬ OrdinaryUniqueSuccessfulPath ordinaryStepAt (expandRuns (fiveWayState 31)) := by
  intro hu
  apply fiveWay_full_not_unique
  have h := (ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode _).mp hu
  simpa only [encode_expandRuns (fiveWay_normalized 31)] using h

end LC004

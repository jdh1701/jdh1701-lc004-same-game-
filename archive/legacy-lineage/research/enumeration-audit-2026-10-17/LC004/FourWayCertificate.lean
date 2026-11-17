import LC004.CertifiedPaths
import LC004.RawEncoding

namespace LC004

/-- Fixed palindromic colour skeleton. The four optional heavy runs are
at indices 1,3,6,8; index 5 is the heavy centre for every mask. -/
def fourWayState (mask : Nat) : RunState :=
  [(0,false), (1,mask.testBit 0), (0,false), (2,mask.testBit 1),
   (1,false), (2,true), (1,mask.testBit 2), (2,false),
   (0,mask.testBit 3), (1,false), (0,false)]

theorem fourWayState_normalized (mask : Nat) :
    Normalized (fourWayState mask) := by
  simp [fourWayState, Normalized]

-- All computations below are reduced by the Lean kernel itself.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fourWay_proper_mask_cards :
    ∀ mask : Fin 15, (solutionPaths (fourWayState mask.val)).card = 1 := by
  decide

theorem fourWay_all_proper_unique (mask : Fin 15) :
    UniqueSuccessfulPath (fourWayState mask.val) := by
  exact (uniqueSuccessfulPath_iff_card_solutionPaths _).mpr
    (fourWay_proper_mask_cards mask)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fourWay_full_mask_card :
    (solutionPaths (fourWayState 15)).card = 91 := by
  decide

theorem fourWay_full_mask_not_unique :
    ¬ UniqueSuccessfulPath (fourWayState 15) := by
  intro hu
  have h1 := (uniqueSuccessfulPath_iff_card_solutionPaths _).mp hu
  have h91 := fourWay_full_mask_card
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fourWay_only_short_path :
    (solutionPaths (fourWayState 15)).filter (fun p => p.length ≤ 6) =
      {[5,4,3,2,1,0]} := by
  decide

theorem fourWay_encoded_raw_witness :
    encode [0,1,1,0,2,2,1,2,2,1,1,2,0,0,1,0] = fourWayState 15 := by
  rfl

theorem fourWay_successful_canonical :
    SuccessfulPath (fourWayState 15) [5,4,3,2,1,0] := by rfl

theorem fourWay_successful_alternate :
    SuccessfulPath (fourWayState 15) [1,1,3,2,2,1,0] := by rfl

#print axioms fourWay_proper_mask_cards
#print axioms fourWay_all_proper_unique
#print axioms fourWay_full_mask_card
#print axioms fourWay_full_mask_not_unique
#print axioms fourWay_only_short_path

end LC004

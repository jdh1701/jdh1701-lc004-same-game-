import LC004.FiveClassGeometryCases2

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 126; shape: rectangle. -/
theorem fiveGeometrySpec126 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,4,5] (fiveOtherRanks [1,2,3,4,5]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase126 : FiveGeometryCase [1,2,3,4,5] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec126).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [1,2,3,4,5] (fiveOtherRanks [1,2,3,4,5]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [1,2,3,4,5] (fiveOtherRanks [1,2,3,4,5])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 127; shape: empty. -/
theorem fiveGeometrySpec127 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,4,6] (fiveOtherRanks [1,2,3,4,6]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase127 : FiveGeometryCase [1,2,3,4,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec127).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec127 x y).mp hxy)

/-- Exhaustive finite relation 128; shape: rectangle. -/
theorem fiveGeometrySpec128 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,4,7] (fiveOtherRanks [1,2,3,4,7]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase128 : FiveGeometryCase [1,2,3,4,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec128).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec128 x y).mp hxy)

/-- Exhaustive finite relation 129; shape: rectangle. -/
theorem fiveGeometrySpec129 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,4,8] (fiveOtherRanks [1,2,3,4,8]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase129 : FiveGeometryCase [1,2,3,4,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec129).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec129 x y).mp hxy)

/-- Exhaustive finite relation 130; shape: empty. -/
theorem fiveGeometrySpec130 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,4,9] (fiveOtherRanks [1,2,3,4,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase130 : FiveGeometryCase [1,2,3,4,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec130).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec130 x y).mp hxy)

/-- Exhaustive finite relation 131; shape: rectangle. -/
theorem fiveGeometrySpec131 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,5,6] (fiveOtherRanks [1,2,3,5,6]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase131 : FiveGeometryCase [1,2,3,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec131).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec131 x y).mp hxy)

/-- Exhaustive finite relation 132; shape: empty. -/
theorem fiveGeometrySpec132 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,5,7] (fiveOtherRanks [1,2,3,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase132 : FiveGeometryCase [1,2,3,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec132).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec132 x y).mp hxy)

/-- Exhaustive finite relation 133; shape: rectangle. -/
theorem fiveGeometrySpec133 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,5,8] (fiveOtherRanks [1,2,3,5,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase133 : FiveGeometryCase [1,2,3,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec133).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec133 x y).mp hxy)

/-- Exhaustive finite relation 134; shape: rectangle. -/
theorem fiveGeometrySpec134 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,5,9] (fiveOtherRanks [1,2,3,5,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase134 : FiveGeometryCase [1,2,3,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec134).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec134 x y).mp hxy)

/-- Exhaustive finite relation 135; shape: fan. -/
theorem fiveGeometrySpec135 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,6,7] (fiveOtherRanks [1,2,3,6,7]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 4)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase135 : FiveGeometryCase [1,2,3,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec135).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (4 : Fin 10))
  · intro _
    refine ⟨9, 4, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 4)) → x = 9 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec135 x y).mp hxy)

/-- Exhaustive finite relation 136; shape: empty. -/
theorem fiveGeometrySpec136 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,6,8] (fiveOtherRanks [1,2,3,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase136 : FiveGeometryCase [1,2,3,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec136).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec136 x y).mp hxy)

/-- Exhaustive finite relation 137; shape: rectangle. -/
theorem fiveGeometrySpec137 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,6,9] (fiveOtherRanks [1,2,3,6,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase137 : FiveGeometryCase [1,2,3,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec137).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec137 x y).mp hxy)

/-- Exhaustive finite relation 138; shape: fan. -/
theorem fiveGeometrySpec138 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,7,8] (fiveOtherRanks [1,2,3,7,8]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 3)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase138 : FiveGeometryCase [1,2,3,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec138).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (3 : Fin 10))
  · intro _
    refine ⟨9, 3, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 3)) → x = 9 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec138 x y).mp hxy)

/-- Exhaustive finite relation 139; shape: empty. -/
theorem fiveGeometrySpec139 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,7,9] (fiveOtherRanks [1,2,3,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase139 : FiveGeometryCase [1,2,3,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec139).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec139 x y).mp hxy)

/-- Exhaustive finite relation 140; shape: rectangle. -/
theorem fiveGeometrySpec140 : ∀ x y : Fin 10,
    FiveCompatible [1,2,3,8,9] (fiveOtherRanks [1,2,3,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase140 : FiveGeometryCase [1,2,3,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec140).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec140 x y).mp hxy)

/-- Exhaustive finite relation 141; shape: rectangle. -/
theorem fiveGeometrySpec141 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,5,6] (fiveOtherRanks [1,2,4,5,6]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase141 : FiveGeometryCase [1,2,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec141).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec141 x y).mp hxy)

/-- Exhaustive finite relation 142; shape: rectangle. -/
theorem fiveGeometrySpec142 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,5,7] (fiveOtherRanks [1,2,4,5,7]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase142 : FiveGeometryCase [1,2,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec142).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec142 x y).mp hxy)

/-- Exhaustive finite relation 143; shape: two_points. -/
theorem fiveGeometrySpec143 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,5,8] (fiveOtherRanks [1,2,4,5,8]) x y ↔ ((x = 0 ∧ y = 7) ∨ (x = 7 ∧ y = 3)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase143 : FiveGeometryCase [1,2,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec143).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (0 : Fin 10) 7 (7 : Fin 10) 3
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 0 ∧ y = 7) ∨ (x = 7 ∧ y = 3)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec143 x y).mp hxy)

/-- Exhaustive finite relation 144; shape: rectangle. -/
theorem fiveGeometrySpec144 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,5,9] (fiveOtherRanks [1,2,4,5,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase144 : FiveGeometryCase [1,2,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec144).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec144 x y).mp hxy)

/-- Exhaustive finite relation 145; shape: empty. -/
theorem fiveGeometrySpec145 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,6,7] (fiveOtherRanks [1,2,4,6,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase145 : FiveGeometryCase [1,2,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec145).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec145 x y).mp hxy)

/-- Exhaustive finite relation 146; shape: empty. -/
theorem fiveGeometrySpec146 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,6,8] (fiveOtherRanks [1,2,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase146 : FiveGeometryCase [1,2,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec146).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec146 x y).mp hxy)

/-- Exhaustive finite relation 147; shape: empty. -/
theorem fiveGeometrySpec147 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,6,9] (fiveOtherRanks [1,2,4,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase147 : FiveGeometryCase [1,2,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec147).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec147 x y).mp hxy)

/-- Exhaustive finite relation 148; shape: rectangle. -/
theorem fiveGeometrySpec148 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,7,8] (fiveOtherRanks [1,2,4,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase148 : FiveGeometryCase [1,2,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec148).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec148 x y).mp hxy)

/-- Exhaustive finite relation 149; shape: empty. -/
theorem fiveGeometrySpec149 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,7,9] (fiveOtherRanks [1,2,4,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase149 : FiveGeometryCase [1,2,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec149).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec149 x y).mp hxy)

/-- Exhaustive finite relation 150; shape: rectangle. -/
theorem fiveGeometrySpec150 : ∀ x y : Fin 10,
    FiveCompatible [1,2,4,8,9] (fiveOtherRanks [1,2,4,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase150 : FiveGeometryCase [1,2,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec150).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec150 x y).mp hxy)

/-- Exhaustive finite relation 151; shape: fan. -/
theorem fiveGeometrySpec151 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,6,7] (fiveOtherRanks [1,2,5,6,7]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 4)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase151 : FiveGeometryCase [1,2,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec151).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (4 : Fin 10))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 4)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec151 x y).mp hxy)

/-- Exhaustive finite relation 152; shape: rectangle. -/
theorem fiveGeometrySpec152 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,6,8] (fiveOtherRanks [1,2,5,6,8]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase152 : FiveGeometryCase [1,2,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec152).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec152 x y).mp hxy)

/-- Exhaustive finite relation 153; shape: rectangle. -/
theorem fiveGeometrySpec153 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,6,9] (fiveOtherRanks [1,2,5,6,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase153 : FiveGeometryCase [1,2,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec153).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec153 x y).mp hxy)

/-- Exhaustive finite relation 154; shape: rectangle. -/
theorem fiveGeometrySpec154 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,7,8] (fiveOtherRanks [1,2,5,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase154 : FiveGeometryCase [1,2,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec154).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec154 x y).mp hxy)

/-- Exhaustive finite relation 155; shape: empty. -/
theorem fiveGeometrySpec155 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,7,9] (fiveOtherRanks [1,2,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase155 : FiveGeometryCase [1,2,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec155).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec155 x y).mp hxy)

/-- Exhaustive finite relation 156; shape: two_points. -/
theorem fiveGeometrySpec156 : ∀ x y : Fin 10,
    FiveCompatible [1,2,5,8,9] (fiveOtherRanks [1,2,5,8,9]) x y ↔ ((x = 0 ∧ y = 9) ∨ (x = 9 ∧ y = 4)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase156 : FiveGeometryCase [1,2,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec156).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (0 : Fin 10) 9 (9 : Fin 10) 4
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 0 ∧ y = 9) ∨ (x = 9 ∧ y = 4)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec156 x y).mp hxy)

/-- Exhaustive finite relation 157; shape: fan. -/
theorem fiveGeometrySpec157 : ∀ x y : Fin 10,
    FiveCompatible [1,2,6,7,8] (fiveOtherRanks [1,2,6,7,8]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 3)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase157 : FiveGeometryCase [1,2,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec157).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (3 : Fin 10))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 3)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec157 x y).mp hxy)

/-- Exhaustive finite relation 158; shape: empty. -/
theorem fiveGeometrySpec158 : ∀ x y : Fin 10,
    FiveCompatible [1,2,6,7,9] (fiveOtherRanks [1,2,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase158 : FiveGeometryCase [1,2,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec158).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec158 x y).mp hxy)

/-- Exhaustive finite relation 159; shape: rectangle. -/
theorem fiveGeometrySpec159 : ∀ x y : Fin 10,
    FiveCompatible [1,2,6,8,9] (fiveOtherRanks [1,2,6,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase159 : FiveGeometryCase [1,2,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec159).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec159 x y).mp hxy)

/-- Exhaustive finite relation 160; shape: rectangle. -/
theorem fiveGeometrySpec160 : ∀ x y : Fin 10,
    FiveCompatible [1,2,7,8,9] (fiveOtherRanks [1,2,7,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase160 : FiveGeometryCase [1,2,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec160).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec160 x y).mp hxy)

/-- Exhaustive finite relation 161; shape: empty. -/
theorem fiveGeometrySpec161 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,5,6] (fiveOtherRanks [1,3,4,5,6]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase161 : FiveGeometryCase [1,3,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec161).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec161 x y).mp hxy)

/-- Exhaustive finite relation 162; shape: rectangle. -/
theorem fiveGeometrySpec162 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,5,7] (fiveOtherRanks [1,3,4,5,7]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase162 : FiveGeometryCase [1,3,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec162).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec162 x y).mp hxy)

/-- Exhaustive finite relation 163; shape: rectangle. -/
theorem fiveGeometrySpec163 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,5,8] (fiveOtherRanks [1,3,4,5,8]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase163 : FiveGeometryCase [1,3,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec163).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec163 x y).mp hxy)

/-- Exhaustive finite relation 164; shape: empty. -/
theorem fiveGeometrySpec164 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,5,9] (fiveOtherRanks [1,3,4,5,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase164 : FiveGeometryCase [1,3,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec164).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec164 x y).mp hxy)

/-- Exhaustive finite relation 165; shape: rectangle. -/
theorem fiveGeometrySpec165 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,6,7] (fiveOtherRanks [1,3,4,6,7]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase165 : FiveGeometryCase [1,3,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec165).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec165 x y).mp hxy)

/-- Exhaustive finite relation 166; shape: empty. -/
theorem fiveGeometrySpec166 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,6,8] (fiveOtherRanks [1,3,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase166 : FiveGeometryCase [1,3,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec166).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec166 x y).mp hxy)

/-- Exhaustive finite relation 167; shape: empty. -/
theorem fiveGeometrySpec167 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,6,9] (fiveOtherRanks [1,3,4,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase167 : FiveGeometryCase [1,3,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec167).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec167 x y).mp hxy)

def fiveGeometryChunk3 : List (List Nat) :=
  [[1,2,3,4,5],
  [1,2,3,4,6],
  [1,2,3,4,7],
  [1,2,3,4,8],
  [1,2,3,4,9],
  [1,2,3,5,6],
  [1,2,3,5,7],
  [1,2,3,5,8],
  [1,2,3,5,9],
  [1,2,3,6,7],
  [1,2,3,6,8],
  [1,2,3,6,9],
  [1,2,3,7,8],
  [1,2,3,7,9],
  [1,2,3,8,9],
  [1,2,4,5,6],
  [1,2,4,5,7],
  [1,2,4,5,8],
  [1,2,4,5,9],
  [1,2,4,6,7],
  [1,2,4,6,8],
  [1,2,4,6,9],
  [1,2,4,7,8],
  [1,2,4,7,9],
  [1,2,4,8,9],
  [1,2,5,6,7],
  [1,2,5,6,8],
  [1,2,5,6,9],
  [1,2,5,7,8],
  [1,2,5,7,9],
  [1,2,5,8,9],
  [1,2,6,7,8],
  [1,2,6,7,9],
  [1,2,6,8,9],
  [1,2,7,8,9],
  [1,3,4,5,6],
  [1,3,4,5,7],
  [1,3,4,5,8],
  [1,3,4,5,9],
  [1,3,4,6,7],
  [1,3,4,6,8],
  [1,3,4,6,9]]

theorem fiveGeometryChunk3_checked : ∀ g ∈ fiveGeometryChunk3, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk3, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase126
  · subst g
    exact fiveGeometryCase127
  · subst g
    exact fiveGeometryCase128
  · subst g
    exact fiveGeometryCase129
  · subst g
    exact fiveGeometryCase130
  · subst g
    exact fiveGeometryCase131
  · subst g
    exact fiveGeometryCase132
  · subst g
    exact fiveGeometryCase133
  · subst g
    exact fiveGeometryCase134
  · subst g
    exact fiveGeometryCase135
  · subst g
    exact fiveGeometryCase136
  · subst g
    exact fiveGeometryCase137
  · subst g
    exact fiveGeometryCase138
  · subst g
    exact fiveGeometryCase139
  · subst g
    exact fiveGeometryCase140
  · subst g
    exact fiveGeometryCase141
  · subst g
    exact fiveGeometryCase142
  · subst g
    exact fiveGeometryCase143
  · subst g
    exact fiveGeometryCase144
  · subst g
    exact fiveGeometryCase145
  · subst g
    exact fiveGeometryCase146
  · subst g
    exact fiveGeometryCase147
  · subst g
    exact fiveGeometryCase148
  · subst g
    exact fiveGeometryCase149
  · subst g
    exact fiveGeometryCase150
  · subst g
    exact fiveGeometryCase151
  · subst g
    exact fiveGeometryCase152
  · subst g
    exact fiveGeometryCase153
  · subst g
    exact fiveGeometryCase154
  · subst g
    exact fiveGeometryCase155
  · subst g
    exact fiveGeometryCase156
  · subst g
    exact fiveGeometryCase157
  · subst g
    exact fiveGeometryCase158
  · subst g
    exact fiveGeometryCase159
  · subst g
    exact fiveGeometryCase160
  · subst g
    exact fiveGeometryCase161
  · subst g
    exact fiveGeometryCase162
  · subst g
    exact fiveGeometryCase163
  · subst g
    exact fiveGeometryCase164
  · subst g
    exact fiveGeometryCase165
  · subst g
    exact fiveGeometryCase166
  · subst g
    exact fiveGeometryCase167

end LC004

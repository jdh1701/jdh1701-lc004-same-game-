import LC004.FiveClassGeometryCases1

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 84; shape: empty. -/
theorem fiveGeometrySpec084 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,7,8] (fiveOtherRanks [0,2,5,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase084 : FiveGeometryCase [0,2,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec084).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec084 x y).mp hxy)

/-- Exhaustive finite relation 85; shape: empty. -/
theorem fiveGeometrySpec085 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,7,9] (fiveOtherRanks [0,2,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase085 : FiveGeometryCase [0,2,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec085).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec085 x y).mp hxy)

/-- Exhaustive finite relation 86; shape: rectangle. -/
theorem fiveGeometrySpec086 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,8,9] (fiveOtherRanks [0,2,5,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase086 : FiveGeometryCase [0,2,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec086).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec086 x y).mp hxy)

/-- Exhaustive finite relation 87; shape: empty. -/
theorem fiveGeometrySpec087 : ∀ x y : Fin 10,
    FiveCompatible [0,2,6,7,8] (fiveOtherRanks [0,2,6,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase087 : FiveGeometryCase [0,2,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec087).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec087 x y).mp hxy)

/-- Exhaustive finite relation 88; shape: rectangle. -/
theorem fiveGeometrySpec088 : ∀ x y : Fin 10,
    FiveCompatible [0,2,6,7,9] (fiveOtherRanks [0,2,6,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase088 : FiveGeometryCase [0,2,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec088).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec088 x y).mp hxy)

/-- Exhaustive finite relation 89; shape: rectangle. -/
theorem fiveGeometrySpec089 : ∀ x y : Fin 10,
    FiveCompatible [0,2,6,8,9] (fiveOtherRanks [0,2,6,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase089 : FiveGeometryCase [0,2,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec089).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec089 x y).mp hxy)

/-- Exhaustive finite relation 90; shape: empty. -/
theorem fiveGeometrySpec090 : ∀ x y : Fin 10,
    FiveCompatible [0,2,7,8,9] (fiveOtherRanks [0,2,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase090 : FiveGeometryCase [0,2,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec090).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec090 x y).mp hxy)

/-- Exhaustive finite relation 91; shape: rectangle. -/
theorem fiveGeometrySpec091 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,5,6] (fiveOtherRanks [0,3,4,5,6]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase091 : FiveGeometryCase [0,3,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec091).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec091 x y).mp hxy)

/-- Exhaustive finite relation 92; shape: rectangle. -/
theorem fiveGeometrySpec092 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,5,7] (fiveOtherRanks [0,3,4,5,7]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase092 : FiveGeometryCase [0,3,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec092).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec092 x y).mp hxy)

/-- Exhaustive finite relation 93; shape: empty. -/
theorem fiveGeometrySpec093 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,5,8] (fiveOtherRanks [0,3,4,5,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase093 : FiveGeometryCase [0,3,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec093).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec093 x y).mp hxy)

/-- Exhaustive finite relation 94; shape: fan. -/
theorem fiveGeometrySpec094 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,5,9] (fiveOtherRanks [0,3,4,5,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 3 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase094 : FiveGeometryCase [0,3,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec094).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (3 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨3, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 3 ∨ y = 0)) → x = 3 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec094 x y).mp hxy)

/-- Exhaustive finite relation 95; shape: two_points. -/
theorem fiveGeometrySpec095 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,6,7] (fiveOtherRanks [0,3,4,6,7]) x y ↔ ((x = 4 ∧ y = 9) ∨ (x = 9 ∧ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase095 : FiveGeometryCase [0,3,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec095).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (4 : Fin 10) 9 (9 : Fin 10) 0
  · intro _
    refine ⟨4, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 4 ∧ y = 9) ∨ (x = 9 ∧ y = 0)) → x = 4 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec095 x y).mp hxy)

/-- Exhaustive finite relation 96; shape: empty. -/
theorem fiveGeometrySpec096 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,6,8] (fiveOtherRanks [0,3,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase096 : FiveGeometryCase [0,3,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec096).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec096 x y).mp hxy)

/-- Exhaustive finite relation 97; shape: rectangle. -/
theorem fiveGeometrySpec097 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,6,9] (fiveOtherRanks [0,3,4,6,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase097 : FiveGeometryCase [0,3,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec097).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec097 x y).mp hxy)

/-- Exhaustive finite relation 98; shape: rectangle. -/
theorem fiveGeometrySpec098 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,7,8] (fiveOtherRanks [0,3,4,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase098 : FiveGeometryCase [0,3,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec098).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec098 x y).mp hxy)

/-- Exhaustive finite relation 99; shape: rectangle. -/
theorem fiveGeometrySpec099 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,7,9] (fiveOtherRanks [0,3,4,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase099 : FiveGeometryCase [0,3,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec099).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec099 x y).mp hxy)

/-- Exhaustive finite relation 100; shape: fan. -/
theorem fiveGeometrySpec100 : ∀ x y : Fin 10,
    FiveCompatible [0,3,4,8,9] (fiveOtherRanks [0,3,4,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 4 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase100 : FiveGeometryCase [0,3,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec100).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (4 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨4, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 4 ∨ y = 0)) → x = 4 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec100 x y).mp hxy)

/-- Exhaustive finite relation 101; shape: rectangle. -/
theorem fiveGeometrySpec101 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,6,7] (fiveOtherRanks [0,3,5,6,7]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase101 : FiveGeometryCase [0,3,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec101).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec101 x y).mp hxy)

/-- Exhaustive finite relation 102; shape: empty. -/
theorem fiveGeometrySpec102 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,6,8] (fiveOtherRanks [0,3,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase102 : FiveGeometryCase [0,3,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec102).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec102 x y).mp hxy)

/-- Exhaustive finite relation 103; shape: rectangle. -/
theorem fiveGeometrySpec103 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,6,9] (fiveOtherRanks [0,3,5,6,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase103 : FiveGeometryCase [0,3,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec103).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec103 x y).mp hxy)

/-- Exhaustive finite relation 104; shape: empty. -/
theorem fiveGeometrySpec104 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,7,8] (fiveOtherRanks [0,3,5,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase104 : FiveGeometryCase [0,3,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec104).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec104 x y).mp hxy)

/-- Exhaustive finite relation 105; shape: empty. -/
theorem fiveGeometrySpec105 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,7,9] (fiveOtherRanks [0,3,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase105 : FiveGeometryCase [0,3,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec105).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec105 x y).mp hxy)

/-- Exhaustive finite relation 106; shape: empty. -/
theorem fiveGeometrySpec106 : ∀ x y : Fin 10,
    FiveCompatible [0,3,5,8,9] (fiveOtherRanks [0,3,5,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase106 : FiveGeometryCase [0,3,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec106).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec106 x y).mp hxy)

/-- Exhaustive finite relation 107; shape: rectangle. -/
theorem fiveGeometrySpec107 : ∀ x y : Fin 10,
    FiveCompatible [0,3,6,7,8] (fiveOtherRanks [0,3,6,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase107 : FiveGeometryCase [0,3,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec107).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec107 x y).mp hxy)

/-- Exhaustive finite relation 108; shape: two_points. -/
theorem fiveGeometrySpec108 : ∀ x y : Fin 10,
    FiveCompatible [0,3,6,7,9] (fiveOtherRanks [0,3,6,7,9]) x y ↔ ((x = 3 ∧ y = 7) ∨ (x = 7 ∧ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase108 : FiveGeometryCase [0,3,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec108).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (3 : Fin 10) 7 (7 : Fin 10) 0
  · intro _
    refine ⟨3, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 3 ∧ y = 7) ∨ (x = 7 ∧ y = 0)) → x = 3 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec108 x y).mp hxy)

/-- Exhaustive finite relation 109; shape: rectangle. -/
theorem fiveGeometrySpec109 : ∀ x y : Fin 10,
    FiveCompatible [0,3,6,8,9] (fiveOtherRanks [0,3,6,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase109 : FiveGeometryCase [0,3,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec109).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec109 x y).mp hxy)

/-- Exhaustive finite relation 110; shape: rectangle. -/
theorem fiveGeometrySpec110 : ∀ x y : Fin 10,
    FiveCompatible [0,3,7,8,9] (fiveOtherRanks [0,3,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase110 : FiveGeometryCase [0,3,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec110).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec110 x y).mp hxy)

/-- Exhaustive finite relation 111; shape: rectangle. -/
theorem fiveGeometrySpec111 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,6,7] (fiveOtherRanks [0,4,5,6,7]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase111 : FiveGeometryCase [0,4,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec111).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec111 x y).mp hxy)

/-- Exhaustive finite relation 112; shape: empty. -/
theorem fiveGeometrySpec112 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,6,8] (fiveOtherRanks [0,4,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase112 : FiveGeometryCase [0,4,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec112).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec112 x y).mp hxy)

/-- Exhaustive finite relation 113; shape: fan. -/
theorem fiveGeometrySpec113 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,6,9] (fiveOtherRanks [0,4,5,6,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 3 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase113 : FiveGeometryCase [0,4,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec113).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (3 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨3, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 3 ∨ y = 9)) → x = 3 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec113 x y).mp hxy)

/-- Exhaustive finite relation 114; shape: rectangle. -/
theorem fiveGeometrySpec114 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,7,8] (fiveOtherRanks [0,4,5,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase114 : FiveGeometryCase [0,4,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec114).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec114 x y).mp hxy)

/-- Exhaustive finite relation 115; shape: empty. -/
theorem fiveGeometrySpec115 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,7,9] (fiveOtherRanks [0,4,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase115 : FiveGeometryCase [0,4,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec115).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec115 x y).mp hxy)

/-- Exhaustive finite relation 116; shape: fan. -/
theorem fiveGeometrySpec116 : ∀ x y : Fin 10,
    FiveCompatible [0,4,5,8,9] (fiveOtherRanks [0,4,5,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 4 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase116 : FiveGeometryCase [0,4,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec116).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (4 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨4, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 4 ∨ y = 9)) → x = 4 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec116 x y).mp hxy)

/-- Exhaustive finite relation 117; shape: rectangle. -/
theorem fiveGeometrySpec117 : ∀ x y : Fin 10,
    FiveCompatible [0,4,6,7,8] (fiveOtherRanks [0,4,6,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase117 : FiveGeometryCase [0,4,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec117).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec117 x y).mp hxy)

/-- Exhaustive finite relation 118; shape: rectangle. -/
theorem fiveGeometrySpec118 : ∀ x y : Fin 10,
    FiveCompatible [0,4,6,7,9] (fiveOtherRanks [0,4,6,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase118 : FiveGeometryCase [0,4,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec118).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec118 x y).mp hxy)

/-- Exhaustive finite relation 119; shape: empty. -/
theorem fiveGeometrySpec119 : ∀ x y : Fin 10,
    FiveCompatible [0,4,6,8,9] (fiveOtherRanks [0,4,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase119 : FiveGeometryCase [0,4,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec119).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec119 x y).mp hxy)

/-- Exhaustive finite relation 120; shape: rectangle. -/
theorem fiveGeometrySpec120 : ∀ x y : Fin 10,
    FiveCompatible [0,4,7,8,9] (fiveOtherRanks [0,4,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase120 : FiveGeometryCase [0,4,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec120).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec120 x y).mp hxy)

/-- Exhaustive finite relation 121; shape: empty. -/
theorem fiveGeometrySpec121 : ∀ x y : Fin 10,
    FiveCompatible [0,5,6,7,8] (fiveOtherRanks [0,5,6,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase121 : FiveGeometryCase [0,5,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec121).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec121 x y).mp hxy)

/-- Exhaustive finite relation 122; shape: rectangle. -/
theorem fiveGeometrySpec122 : ∀ x y : Fin 10,
    FiveCompatible [0,5,6,7,9] (fiveOtherRanks [0,5,6,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase122 : FiveGeometryCase [0,5,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec122).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨3, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 3 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec122 x y).mp hxy)

/-- Exhaustive finite relation 123; shape: rectangle. -/
theorem fiveGeometrySpec123 : ∀ x y : Fin 10,
    FiveCompatible [0,5,6,8,9] (fiveOtherRanks [0,5,6,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase123 : FiveGeometryCase [0,5,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec123).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨4, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 4 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec123 x y).mp hxy)

/-- Exhaustive finite relation 124; shape: empty. -/
theorem fiveGeometrySpec124 : ∀ x y : Fin 10,
    FiveCompatible [0,5,7,8,9] (fiveOtherRanks [0,5,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase124 : FiveGeometryCase [0,5,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec124).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec124 x y).mp hxy)

/-- Exhaustive finite relation 125; shape: rectangle. -/
theorem fiveGeometrySpec125 : ∀ x y : Fin 10,
    FiveCompatible [0,6,7,8,9] (fiveOtherRanks [0,6,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase125 : FiveGeometryCase [0,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec125).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [0,6,7,8,9] (fiveOtherRanks [0,6,7,8,9]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [0,6,7,8,9] (fiveOtherRanks [0,6,7,8,9])).mpr hc
    rw [hn] at ht
    contradiction

def fiveGeometryChunk2 : List (List Nat) :=
  [[0,2,5,7,8],
  [0,2,5,7,9],
  [0,2,5,8,9],
  [0,2,6,7,8],
  [0,2,6,7,9],
  [0,2,6,8,9],
  [0,2,7,8,9],
  [0,3,4,5,6],
  [0,3,4,5,7],
  [0,3,4,5,8],
  [0,3,4,5,9],
  [0,3,4,6,7],
  [0,3,4,6,8],
  [0,3,4,6,9],
  [0,3,4,7,8],
  [0,3,4,7,9],
  [0,3,4,8,9],
  [0,3,5,6,7],
  [0,3,5,6,8],
  [0,3,5,6,9],
  [0,3,5,7,8],
  [0,3,5,7,9],
  [0,3,5,8,9],
  [0,3,6,7,8],
  [0,3,6,7,9],
  [0,3,6,8,9],
  [0,3,7,8,9],
  [0,4,5,6,7],
  [0,4,5,6,8],
  [0,4,5,6,9],
  [0,4,5,7,8],
  [0,4,5,7,9],
  [0,4,5,8,9],
  [0,4,6,7,8],
  [0,4,6,7,9],
  [0,4,6,8,9],
  [0,4,7,8,9],
  [0,5,6,7,8],
  [0,5,6,7,9],
  [0,5,6,8,9],
  [0,5,7,8,9],
  [0,6,7,8,9]]

theorem fiveGeometryChunk2_checked : ∀ g ∈ fiveGeometryChunk2, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk2, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase084
  · subst g
    exact fiveGeometryCase085
  · subst g
    exact fiveGeometryCase086
  · subst g
    exact fiveGeometryCase087
  · subst g
    exact fiveGeometryCase088
  · subst g
    exact fiveGeometryCase089
  · subst g
    exact fiveGeometryCase090
  · subst g
    exact fiveGeometryCase091
  · subst g
    exact fiveGeometryCase092
  · subst g
    exact fiveGeometryCase093
  · subst g
    exact fiveGeometryCase094
  · subst g
    exact fiveGeometryCase095
  · subst g
    exact fiveGeometryCase096
  · subst g
    exact fiveGeometryCase097
  · subst g
    exact fiveGeometryCase098
  · subst g
    exact fiveGeometryCase099
  · subst g
    exact fiveGeometryCase100
  · subst g
    exact fiveGeometryCase101
  · subst g
    exact fiveGeometryCase102
  · subst g
    exact fiveGeometryCase103
  · subst g
    exact fiveGeometryCase104
  · subst g
    exact fiveGeometryCase105
  · subst g
    exact fiveGeometryCase106
  · subst g
    exact fiveGeometryCase107
  · subst g
    exact fiveGeometryCase108
  · subst g
    exact fiveGeometryCase109
  · subst g
    exact fiveGeometryCase110
  · subst g
    exact fiveGeometryCase111
  · subst g
    exact fiveGeometryCase112
  · subst g
    exact fiveGeometryCase113
  · subst g
    exact fiveGeometryCase114
  · subst g
    exact fiveGeometryCase115
  · subst g
    exact fiveGeometryCase116
  · subst g
    exact fiveGeometryCase117
  · subst g
    exact fiveGeometryCase118
  · subst g
    exact fiveGeometryCase119
  · subst g
    exact fiveGeometryCase120
  · subst g
    exact fiveGeometryCase121
  · subst g
    exact fiveGeometryCase122
  · subst g
    exact fiveGeometryCase123
  · subst g
    exact fiveGeometryCase124
  · subst g
    exact fiveGeometryCase125

end LC004

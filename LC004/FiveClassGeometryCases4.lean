import LC004.FiveClassGeometryCases3

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 168; shape: rectangle. -/
theorem fiveGeometrySpec168 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,7,8] (fiveOtherRanks [1,3,4,7,8]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase168 : FiveGeometryCase [1,3,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec168).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec168 x y).mp hxy)

/-- Exhaustive finite relation 169; shape: empty. -/
theorem fiveGeometrySpec169 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,7,9] (fiveOtherRanks [1,3,4,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase169 : FiveGeometryCase [1,3,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec169).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec169 x y).mp hxy)

/-- Exhaustive finite relation 170; shape: empty. -/
theorem fiveGeometrySpec170 : ∀ x y : Fin 10,
    FiveCompatible [1,3,4,8,9] (fiveOtherRanks [1,3,4,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase170 : FiveGeometryCase [1,3,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec170).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec170 x y).mp hxy)

/-- Exhaustive finite relation 171; shape: empty. -/
theorem fiveGeometrySpec171 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,6,7] (fiveOtherRanks [1,3,5,6,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase171 : FiveGeometryCase [1,3,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec171).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec171 x y).mp hxy)

/-- Exhaustive finite relation 172; shape: empty. -/
theorem fiveGeometrySpec172 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,6,8] (fiveOtherRanks [1,3,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase172 : FiveGeometryCase [1,3,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec172).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec172 x y).mp hxy)

/-- Exhaustive finite relation 173; shape: empty. -/
theorem fiveGeometrySpec173 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,6,9] (fiveOtherRanks [1,3,5,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase173 : FiveGeometryCase [1,3,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec173).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec173 x y).mp hxy)

/-- Exhaustive finite relation 174; shape: empty. -/
theorem fiveGeometrySpec174 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,7,8] (fiveOtherRanks [1,3,5,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase174 : FiveGeometryCase [1,3,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec174).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec174 x y).mp hxy)

/-- Exhaustive finite relation 175; shape: empty. -/
theorem fiveGeometrySpec175 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,7,9] (fiveOtherRanks [1,3,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase175 : FiveGeometryCase [1,3,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec175).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec175 x y).mp hxy)

/-- Exhaustive finite relation 176; shape: empty. -/
theorem fiveGeometrySpec176 : ∀ x y : Fin 10,
    FiveCompatible [1,3,5,8,9] (fiveOtherRanks [1,3,5,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase176 : FiveGeometryCase [1,3,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec176).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec176 x y).mp hxy)

/-- Exhaustive finite relation 177; shape: empty. -/
theorem fiveGeometrySpec177 : ∀ x y : Fin 10,
    FiveCompatible [1,3,6,7,8] (fiveOtherRanks [1,3,6,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase177 : FiveGeometryCase [1,3,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec177).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec177 x y).mp hxy)

/-- Exhaustive finite relation 178; shape: empty. -/
theorem fiveGeometrySpec178 : ∀ x y : Fin 10,
    FiveCompatible [1,3,6,7,9] (fiveOtherRanks [1,3,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase178 : FiveGeometryCase [1,3,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec178).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec178 x y).mp hxy)

/-- Exhaustive finite relation 179; shape: empty. -/
theorem fiveGeometrySpec179 : ∀ x y : Fin 10,
    FiveCompatible [1,3,6,8,9] (fiveOtherRanks [1,3,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase179 : FiveGeometryCase [1,3,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec179).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec179 x y).mp hxy)

/-- Exhaustive finite relation 180; shape: empty. -/
theorem fiveGeometrySpec180 : ∀ x y : Fin 10,
    FiveCompatible [1,3,7,8,9] (fiveOtherRanks [1,3,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase180 : FiveGeometryCase [1,3,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec180).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec180 x y).mp hxy)

/-- Exhaustive finite relation 181; shape: rectangle. -/
theorem fiveGeometrySpec181 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,6,7] (fiveOtherRanks [1,4,5,6,7]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase181 : FiveGeometryCase [1,4,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec181).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec181 x y).mp hxy)

/-- Exhaustive finite relation 182; shape: rectangle. -/
theorem fiveGeometrySpec182 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,6,8] (fiveOtherRanks [1,4,5,6,8]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase182 : FiveGeometryCase [1,4,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec182).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec182 x y).mp hxy)

/-- Exhaustive finite relation 183; shape: empty. -/
theorem fiveGeometrySpec183 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,6,9] (fiveOtherRanks [1,4,5,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase183 : FiveGeometryCase [1,4,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec183).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec183 x y).mp hxy)

/-- Exhaustive finite relation 184; shape: two_points. -/
theorem fiveGeometrySpec184 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,7,8] (fiveOtherRanks [1,4,5,7,8]) x y ↔ ((x = 4 ∧ y = 3) ∨ (x = 9 ∧ y = 4)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase184 : FiveGeometryCase [1,4,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec184).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (4 : Fin 10) 9 (3 : Fin 10) 4
  · intro _
    refine ⟨4, 4, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 4 ∧ y = 3) ∨ (x = 9 ∧ y = 4)) → x = 4 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec184 x y).mp hxy)

/-- Exhaustive finite relation 185; shape: empty. -/
theorem fiveGeometrySpec185 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,7,9] (fiveOtherRanks [1,4,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase185 : FiveGeometryCase [1,4,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec185).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec185 x y).mp hxy)

/-- Exhaustive finite relation 186; shape: rectangle. -/
theorem fiveGeometrySpec186 : ∀ x y : Fin 10,
    FiveCompatible [1,4,5,8,9] (fiveOtherRanks [1,4,5,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase186 : FiveGeometryCase [1,4,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec186).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec186 x y).mp hxy)

/-- Exhaustive finite relation 187; shape: rectangle. -/
theorem fiveGeometrySpec187 : ∀ x y : Fin 10,
    FiveCompatible [1,4,6,7,8] (fiveOtherRanks [1,4,6,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase187 : FiveGeometryCase [1,4,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec187).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec187 x y).mp hxy)

/-- Exhaustive finite relation 188; shape: empty. -/
theorem fiveGeometrySpec188 : ∀ x y : Fin 10,
    FiveCompatible [1,4,6,7,9] (fiveOtherRanks [1,4,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase188 : FiveGeometryCase [1,4,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec188).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec188 x y).mp hxy)

/-- Exhaustive finite relation 189; shape: empty. -/
theorem fiveGeometrySpec189 : ∀ x y : Fin 10,
    FiveCompatible [1,4,6,8,9] (fiveOtherRanks [1,4,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase189 : FiveGeometryCase [1,4,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec189).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec189 x y).mp hxy)

/-- Exhaustive finite relation 190; shape: rectangle. -/
theorem fiveGeometrySpec190 : ∀ x y : Fin 10,
    FiveCompatible [1,4,7,8,9] (fiveOtherRanks [1,4,7,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase190 : FiveGeometryCase [1,4,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec190).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec190 x y).mp hxy)

/-- Exhaustive finite relation 191; shape: rectangle. -/
theorem fiveGeometrySpec191 : ∀ x y : Fin 10,
    FiveCompatible [1,5,6,7,8] (fiveOtherRanks [1,5,6,7,8]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase191 : FiveGeometryCase [1,5,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec191).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec191 x y).mp hxy)

/-- Exhaustive finite relation 192; shape: empty. -/
theorem fiveGeometrySpec192 : ∀ x y : Fin 10,
    FiveCompatible [1,5,6,7,9] (fiveOtherRanks [1,5,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase192 : FiveGeometryCase [1,5,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec192).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec192 x y).mp hxy)

/-- Exhaustive finite relation 193; shape: rectangle. -/
theorem fiveGeometrySpec193 : ∀ x y : Fin 10,
    FiveCompatible [1,5,6,8,9] (fiveOtherRanks [1,5,6,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase193 : FiveGeometryCase [1,5,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec193).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec193 x y).mp hxy)

/-- Exhaustive finite relation 194; shape: rectangle. -/
theorem fiveGeometrySpec194 : ∀ x y : Fin 10,
    FiveCompatible [1,5,7,8,9] (fiveOtherRanks [1,5,7,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase194 : FiveGeometryCase [1,5,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec194).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec194 x y).mp hxy)

/-- Exhaustive finite relation 195; shape: empty. -/
theorem fiveGeometrySpec195 : ∀ x y : Fin 10,
    FiveCompatible [1,6,7,8,9] (fiveOtherRanks [1,6,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase195 : FiveGeometryCase [1,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec195).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec195 x y).mp hxy)

/-- Exhaustive finite relation 196; shape: rectangle. -/
theorem fiveGeometrySpec196 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,5,6] (fiveOtherRanks [2,3,4,5,6]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase196 : FiveGeometryCase [2,3,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec196).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [2,3,4,5,6] (fiveOtherRanks [2,3,4,5,6]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [2,3,4,5,6] (fiveOtherRanks [2,3,4,5,6])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 197; shape: empty. -/
theorem fiveGeometrySpec197 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,5,7] (fiveOtherRanks [2,3,4,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase197 : FiveGeometryCase [2,3,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec197).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec197 x y).mp hxy)

/-- Exhaustive finite relation 198; shape: rectangle. -/
theorem fiveGeometrySpec198 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,5,8] (fiveOtherRanks [2,3,4,5,8]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase198 : FiveGeometryCase [2,3,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec198).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec198 x y).mp hxy)

/-- Exhaustive finite relation 199; shape: rectangle. -/
theorem fiveGeometrySpec199 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,5,9] (fiveOtherRanks [2,3,4,5,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase199 : FiveGeometryCase [2,3,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec199).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec199 x y).mp hxy)

/-- Exhaustive finite relation 200; shape: rectangle. -/
theorem fiveGeometrySpec200 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,6,7] (fiveOtherRanks [2,3,4,6,7]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase200 : FiveGeometryCase [2,3,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec200).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec200 x y).mp hxy)

/-- Exhaustive finite relation 201; shape: empty. -/
theorem fiveGeometrySpec201 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,6,8] (fiveOtherRanks [2,3,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase201 : FiveGeometryCase [2,3,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec201).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec201 x y).mp hxy)

/-- Exhaustive finite relation 202; shape: rectangle. -/
theorem fiveGeometrySpec202 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,6,9] (fiveOtherRanks [2,3,4,6,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase202 : FiveGeometryCase [2,3,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec202).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec202 x y).mp hxy)

/-- Exhaustive finite relation 203; shape: fan. -/
theorem fiveGeometrySpec203 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,7,8] (fiveOtherRanks [2,3,4,7,8]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 7)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase203 : FiveGeometryCase [2,3,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec203).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (7 : Fin 10))
  · intro _
    refine ⟨9, 7, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 7)) → x = 9 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec203 x y).mp hxy)

/-- Exhaustive finite relation 204; shape: empty. -/
theorem fiveGeometrySpec204 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,7,9] (fiveOtherRanks [2,3,4,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase204 : FiveGeometryCase [2,3,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec204).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec204 x y).mp hxy)

/-- Exhaustive finite relation 205; shape: fan. -/
theorem fiveGeometrySpec205 : ∀ x y : Fin 10,
    FiveCompatible [2,3,4,8,9] (fiveOtherRanks [2,3,4,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase205 : FiveGeometryCase [2,3,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec205).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 0)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec205 x y).mp hxy)

/-- Exhaustive finite relation 206; shape: rectangle. -/
theorem fiveGeometrySpec206 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,6,7] (fiveOtherRanks [2,3,5,6,7]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase206 : FiveGeometryCase [2,3,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec206).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec206 x y).mp hxy)

/-- Exhaustive finite relation 207; shape: rectangle. -/
theorem fiveGeometrySpec207 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,6,8] (fiveOtherRanks [2,3,5,6,8]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase207 : FiveGeometryCase [2,3,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec207).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec207 x y).mp hxy)

/-- Exhaustive finite relation 208; shape: two_points. -/
theorem fiveGeometrySpec208 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,6,9] (fiveOtherRanks [2,3,5,6,9]) x y ↔ ((x = 0 ∧ y = 9) ∨ (x = 7 ∧ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase208 : FiveGeometryCase [2,3,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec208).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (0 : Fin 10) 7 (9 : Fin 10) 0
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 0 ∧ y = 9) ∨ (x = 7 ∧ y = 0)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec208 x y).mp hxy)

/-- Exhaustive finite relation 209; shape: empty. -/
theorem fiveGeometrySpec209 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,7,8] (fiveOtherRanks [2,3,5,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase209 : FiveGeometryCase [2,3,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec209).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec209 x y).mp hxy)

def fiveGeometryChunk4 : List (List Nat) :=
  [[1,3,4,7,8],
  [1,3,4,7,9],
  [1,3,4,8,9],
  [1,3,5,6,7],
  [1,3,5,6,8],
  [1,3,5,6,9],
  [1,3,5,7,8],
  [1,3,5,7,9],
  [1,3,5,8,9],
  [1,3,6,7,8],
  [1,3,6,7,9],
  [1,3,6,8,9],
  [1,3,7,8,9],
  [1,4,5,6,7],
  [1,4,5,6,8],
  [1,4,5,6,9],
  [1,4,5,7,8],
  [1,4,5,7,9],
  [1,4,5,8,9],
  [1,4,6,7,8],
  [1,4,6,7,9],
  [1,4,6,8,9],
  [1,4,7,8,9],
  [1,5,6,7,8],
  [1,5,6,7,9],
  [1,5,6,8,9],
  [1,5,7,8,9],
  [1,6,7,8,9],
  [2,3,4,5,6],
  [2,3,4,5,7],
  [2,3,4,5,8],
  [2,3,4,5,9],
  [2,3,4,6,7],
  [2,3,4,6,8],
  [2,3,4,6,9],
  [2,3,4,7,8],
  [2,3,4,7,9],
  [2,3,4,8,9],
  [2,3,5,6,7],
  [2,3,5,6,8],
  [2,3,5,6,9],
  [2,3,5,7,8]]

theorem fiveGeometryChunk4_checked : ∀ g ∈ fiveGeometryChunk4, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk4, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase168
  · subst g
    exact fiveGeometryCase169
  · subst g
    exact fiveGeometryCase170
  · subst g
    exact fiveGeometryCase171
  · subst g
    exact fiveGeometryCase172
  · subst g
    exact fiveGeometryCase173
  · subst g
    exact fiveGeometryCase174
  · subst g
    exact fiveGeometryCase175
  · subst g
    exact fiveGeometryCase176
  · subst g
    exact fiveGeometryCase177
  · subst g
    exact fiveGeometryCase178
  · subst g
    exact fiveGeometryCase179
  · subst g
    exact fiveGeometryCase180
  · subst g
    exact fiveGeometryCase181
  · subst g
    exact fiveGeometryCase182
  · subst g
    exact fiveGeometryCase183
  · subst g
    exact fiveGeometryCase184
  · subst g
    exact fiveGeometryCase185
  · subst g
    exact fiveGeometryCase186
  · subst g
    exact fiveGeometryCase187
  · subst g
    exact fiveGeometryCase188
  · subst g
    exact fiveGeometryCase189
  · subst g
    exact fiveGeometryCase190
  · subst g
    exact fiveGeometryCase191
  · subst g
    exact fiveGeometryCase192
  · subst g
    exact fiveGeometryCase193
  · subst g
    exact fiveGeometryCase194
  · subst g
    exact fiveGeometryCase195
  · subst g
    exact fiveGeometryCase196
  · subst g
    exact fiveGeometryCase197
  · subst g
    exact fiveGeometryCase198
  · subst g
    exact fiveGeometryCase199
  · subst g
    exact fiveGeometryCase200
  · subst g
    exact fiveGeometryCase201
  · subst g
    exact fiveGeometryCase202
  · subst g
    exact fiveGeometryCase203
  · subst g
    exact fiveGeometryCase204
  · subst g
    exact fiveGeometryCase205
  · subst g
    exact fiveGeometryCase206
  · subst g
    exact fiveGeometryCase207
  · subst g
    exact fiveGeometryCase208
  · subst g
    exact fiveGeometryCase209

end LC004

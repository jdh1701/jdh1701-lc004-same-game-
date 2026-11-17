import LC004.FiveClassGeometryCases4

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 210; shape: empty. -/
theorem fiveGeometrySpec210 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,7,9] (fiveOtherRanks [2,3,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase210 : FiveGeometryCase [2,3,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec210).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec210 x y).mp hxy)

/-- Exhaustive finite relation 211; shape: rectangle. -/
theorem fiveGeometrySpec211 : ∀ x y : Fin 10,
    FiveCompatible [2,3,5,8,9] (fiveOtherRanks [2,3,5,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase211 : FiveGeometryCase [2,3,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec211).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec211 x y).mp hxy)

/-- Exhaustive finite relation 212; shape: fan. -/
theorem fiveGeometrySpec212 : ∀ x y : Fin 10,
    FiveCompatible [2,3,6,7,8] (fiveOtherRanks [2,3,6,7,8]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 7)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase212 : FiveGeometryCase [2,3,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec212).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (7 : Fin 10))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 7)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec212 x y).mp hxy)

/-- Exhaustive finite relation 213; shape: rectangle. -/
theorem fiveGeometrySpec213 : ∀ x y : Fin 10,
    FiveCompatible [2,3,6,7,9] (fiveOtherRanks [2,3,6,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase213 : FiveGeometryCase [2,3,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec213).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec213 x y).mp hxy)

/-- Exhaustive finite relation 214; shape: rectangle. -/
theorem fiveGeometrySpec214 : ∀ x y : Fin 10,
    FiveCompatible [2,3,6,8,9] (fiveOtherRanks [2,3,6,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase214 : FiveGeometryCase [2,3,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec214).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec214 x y).mp hxy)

/-- Exhaustive finite relation 215; shape: fan. -/
theorem fiveGeometrySpec215 : ∀ x y : Fin 10,
    FiveCompatible [2,3,7,8,9] (fiveOtherRanks [2,3,7,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase215 : FiveGeometryCase [2,3,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec215).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 0)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec215 x y).mp hxy)

/-- Exhaustive finite relation 216; shape: empty. -/
theorem fiveGeometrySpec216 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,6,7] (fiveOtherRanks [2,4,5,6,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase216 : FiveGeometryCase [2,4,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec216).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec216 x y).mp hxy)

/-- Exhaustive finite relation 217; shape: rectangle. -/
theorem fiveGeometrySpec217 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,6,8] (fiveOtherRanks [2,4,5,6,8]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase217 : FiveGeometryCase [2,4,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec217).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec217 x y).mp hxy)

/-- Exhaustive finite relation 218; shape: rectangle. -/
theorem fiveGeometrySpec218 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,6,9] (fiveOtherRanks [2,4,5,6,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase218 : FiveGeometryCase [2,4,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec218).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec218 x y).mp hxy)

/-- Exhaustive finite relation 219; shape: rectangle. -/
theorem fiveGeometrySpec219 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,7,8] (fiveOtherRanks [2,4,5,7,8]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase219 : FiveGeometryCase [2,4,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec219).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec219 x y).mp hxy)

/-- Exhaustive finite relation 220; shape: empty. -/
theorem fiveGeometrySpec220 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,7,9] (fiveOtherRanks [2,4,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase220 : FiveGeometryCase [2,4,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec220).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec220 x y).mp hxy)

/-- Exhaustive finite relation 221; shape: rectangle. -/
theorem fiveGeometrySpec221 : ∀ x y : Fin 10,
    FiveCompatible [2,4,5,8,9] (fiveOtherRanks [2,4,5,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase221 : FiveGeometryCase [2,4,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec221).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec221 x y).mp hxy)

/-- Exhaustive finite relation 222; shape: empty. -/
theorem fiveGeometrySpec222 : ∀ x y : Fin 10,
    FiveCompatible [2,4,6,7,8] (fiveOtherRanks [2,4,6,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase222 : FiveGeometryCase [2,4,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec222).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec222 x y).mp hxy)

/-- Exhaustive finite relation 223; shape: empty. -/
theorem fiveGeometrySpec223 : ∀ x y : Fin 10,
    FiveCompatible [2,4,6,7,9] (fiveOtherRanks [2,4,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase223 : FiveGeometryCase [2,4,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec223).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec223 x y).mp hxy)

/-- Exhaustive finite relation 224; shape: empty. -/
theorem fiveGeometrySpec224 : ∀ x y : Fin 10,
    FiveCompatible [2,4,6,8,9] (fiveOtherRanks [2,4,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase224 : FiveGeometryCase [2,4,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec224).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec224 x y).mp hxy)

/-- Exhaustive finite relation 225; shape: empty. -/
theorem fiveGeometrySpec225 : ∀ x y : Fin 10,
    FiveCompatible [2,4,7,8,9] (fiveOtherRanks [2,4,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase225 : FiveGeometryCase [2,4,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec225).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec225 x y).mp hxy)

/-- Exhaustive finite relation 226; shape: rectangle. -/
theorem fiveGeometrySpec226 : ∀ x y : Fin 10,
    FiveCompatible [2,5,6,7,8] (fiveOtherRanks [2,5,6,7,8]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase226 : FiveGeometryCase [2,5,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec226).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec226 x y).mp hxy)

/-- Exhaustive finite relation 227; shape: rectangle. -/
theorem fiveGeometrySpec227 : ∀ x y : Fin 10,
    FiveCompatible [2,5,6,7,9] (fiveOtherRanks [2,5,6,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase227 : FiveGeometryCase [2,5,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec227).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec227 x y).mp hxy)

/-- Exhaustive finite relation 228; shape: two_points. -/
theorem fiveGeometrySpec228 : ∀ x y : Fin 10,
    FiveCompatible [2,5,6,8,9] (fiveOtherRanks [2,5,6,8,9]) x y ↔ ((x = 4 ∧ y = 0) ∨ (x = 9 ∧ y = 7)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase228 : FiveGeometryCase [2,5,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec228).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (4 : Fin 10) 9 (0 : Fin 10) 7
  · intro _
    refine ⟨4, 7, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 4 ∧ y = 0) ∨ (x = 9 ∧ y = 7)) → x = 4 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec228 x y).mp hxy)

/-- Exhaustive finite relation 229; shape: rectangle. -/
theorem fiveGeometrySpec229 : ∀ x y : Fin 10,
    FiveCompatible [2,5,7,8,9] (fiveOtherRanks [2,5,7,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase229 : FiveGeometryCase [2,5,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec229).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec229 x y).mp hxy)

/-- Exhaustive finite relation 230; shape: rectangle. -/
theorem fiveGeometrySpec230 : ∀ x y : Fin 10,
    FiveCompatible [2,6,7,8,9] (fiveOtherRanks [2,6,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase230 : FiveGeometryCase [2,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec230).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec230 x y).mp hxy)

/-- Exhaustive finite relation 231; shape: rectangle. -/
theorem fiveGeometrySpec231 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,6,7] (fiveOtherRanks [3,4,5,6,7]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase231 : FiveGeometryCase [3,4,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec231).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [3,4,5,6,7] (fiveOtherRanks [3,4,5,6,7]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [3,4,5,6,7] (fiveOtherRanks [3,4,5,6,7])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 232; shape: empty. -/
theorem fiveGeometrySpec232 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,6,8] (fiveOtherRanks [3,4,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase232 : FiveGeometryCase [3,4,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec232).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec232 x y).mp hxy)

/-- Exhaustive finite relation 233; shape: rectangle. -/
theorem fiveGeometrySpec233 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,6,9] (fiveOtherRanks [3,4,5,6,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase233 : FiveGeometryCase [3,4,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec233).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec233 x y).mp hxy)

/-- Exhaustive finite relation 234; shape: rectangle. -/
theorem fiveGeometrySpec234 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,7,8] (fiveOtherRanks [3,4,5,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase234 : FiveGeometryCase [3,4,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec234).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec234 x y).mp hxy)

/-- Exhaustive finite relation 235; shape: empty. -/
theorem fiveGeometrySpec235 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,7,9] (fiveOtherRanks [3,4,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase235 : FiveGeometryCase [3,4,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec235).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec235 x y).mp hxy)

/-- Exhaustive finite relation 236; shape: fan. -/
theorem fiveGeometrySpec236 : ∀ x y : Fin 10,
    FiveCompatible [3,4,5,8,9] (fiveOtherRanks [3,4,5,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase236 : FiveGeometryCase [3,4,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec236).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨9, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 9)) → x = 9 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec236 x y).mp hxy)

/-- Exhaustive finite relation 237; shape: rectangle. -/
theorem fiveGeometrySpec237 : ∀ x y : Fin 10,
    FiveCompatible [3,4,6,7,8] (fiveOtherRanks [3,4,6,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase237 : FiveGeometryCase [3,4,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec237).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec237 x y).mp hxy)

/-- Exhaustive finite relation 238; shape: rectangle. -/
theorem fiveGeometrySpec238 : ∀ x y : Fin 10,
    FiveCompatible [3,4,6,7,9] (fiveOtherRanks [3,4,6,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase238 : FiveGeometryCase [3,4,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec238).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec238 x y).mp hxy)

/-- Exhaustive finite relation 239; shape: empty. -/
theorem fiveGeometrySpec239 : ∀ x y : Fin 10,
    FiveCompatible [3,4,6,8,9] (fiveOtherRanks [3,4,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase239 : FiveGeometryCase [3,4,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec239).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec239 x y).mp hxy)

/-- Exhaustive finite relation 240; shape: fan. -/
theorem fiveGeometrySpec240 : ∀ x y : Fin 10,
    FiveCompatible [3,4,7,8,9] (fiveOtherRanks [3,4,7,8,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase240 : FiveGeometryCase [3,4,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec240).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 9)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec240 x y).mp hxy)

/-- Exhaustive finite relation 241; shape: empty. -/
theorem fiveGeometrySpec241 : ∀ x y : Fin 10,
    FiveCompatible [3,5,6,7,8] (fiveOtherRanks [3,5,6,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase241 : FiveGeometryCase [3,5,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec241).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec241 x y).mp hxy)

/-- Exhaustive finite relation 242; shape: rectangle. -/
theorem fiveGeometrySpec242 : ∀ x y : Fin 10,
    FiveCompatible [3,5,6,7,9] (fiveOtherRanks [3,5,6,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase242 : FiveGeometryCase [3,5,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec242).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec242 x y).mp hxy)

/-- Exhaustive finite relation 243; shape: rectangle. -/
theorem fiveGeometrySpec243 : ∀ x y : Fin 10,
    FiveCompatible [3,5,6,8,9] (fiveOtherRanks [3,5,6,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase243 : FiveGeometryCase [3,5,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec243).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec243 x y).mp hxy)

/-- Exhaustive finite relation 244; shape: empty. -/
theorem fiveGeometrySpec244 : ∀ x y : Fin 10,
    FiveCompatible [3,5,7,8,9] (fiveOtherRanks [3,5,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase244 : FiveGeometryCase [3,5,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec244).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec244 x y).mp hxy)

/-- Exhaustive finite relation 245; shape: rectangle. -/
theorem fiveGeometrySpec245 : ∀ x y : Fin 10,
    FiveCompatible [3,6,7,8,9] (fiveOtherRanks [3,6,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase245 : FiveGeometryCase [3,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec245).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec245 x y).mp hxy)

/-- Exhaustive finite relation 246; shape: rectangle. -/
theorem fiveGeometrySpec246 : ∀ x y : Fin 10,
    FiveCompatible [4,5,6,7,8] (fiveOtherRanks [4,5,6,7,8]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase246 : FiveGeometryCase [4,5,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec246).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [4,5,6,7,8] (fiveOtherRanks [4,5,6,7,8]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [4,5,6,7,8] (fiveOtherRanks [4,5,6,7,8])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 247; shape: empty. -/
theorem fiveGeometrySpec247 : ∀ x y : Fin 10,
    FiveCompatible [4,5,6,7,9] (fiveOtherRanks [4,5,6,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase247 : FiveGeometryCase [4,5,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec247).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec247 x y).mp hxy)

/-- Exhaustive finite relation 248; shape: rectangle. -/
theorem fiveGeometrySpec248 : ∀ x y : Fin 10,
    FiveCompatible [4,5,6,8,9] (fiveOtherRanks [4,5,6,8,9]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase248 : FiveGeometryCase [4,5,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec248).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec248 x y).mp hxy)

/-- Exhaustive finite relation 249; shape: rectangle. -/
theorem fiveGeometrySpec249 : ∀ x y : Fin 10,
    FiveCompatible [4,5,7,8,9] (fiveOtherRanks [4,5,7,8,9]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase249 : FiveGeometryCase [4,5,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec249).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec249 x y).mp hxy)

/-- Exhaustive finite relation 250; shape: empty. -/
theorem fiveGeometrySpec250 : ∀ x y : Fin 10,
    FiveCompatible [4,6,7,8,9] (fiveOtherRanks [4,6,7,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase250 : FiveGeometryCase [4,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec250).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec250 x y).mp hxy)

/-- Exhaustive finite relation 251; shape: rectangle. -/
theorem fiveGeometrySpec251 : ∀ x y : Fin 10,
    FiveCompatible [5,6,7,8,9] (fiveOtherRanks [5,6,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase251 : FiveGeometryCase [5,6,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec251).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [5,6,7,8,9] (fiveOtherRanks [5,6,7,8,9]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [5,6,7,8,9] (fiveOtherRanks [5,6,7,8,9])).mpr hc
    rw [hn] at ht
    contradiction

def fiveGeometryChunk5 : List (List Nat) :=
  [[2,3,5,7,9],
  [2,3,5,8,9],
  [2,3,6,7,8],
  [2,3,6,7,9],
  [2,3,6,8,9],
  [2,3,7,8,9],
  [2,4,5,6,7],
  [2,4,5,6,8],
  [2,4,5,6,9],
  [2,4,5,7,8],
  [2,4,5,7,9],
  [2,4,5,8,9],
  [2,4,6,7,8],
  [2,4,6,7,9],
  [2,4,6,8,9],
  [2,4,7,8,9],
  [2,5,6,7,8],
  [2,5,6,7,9],
  [2,5,6,8,9],
  [2,5,7,8,9],
  [2,6,7,8,9],
  [3,4,5,6,7],
  [3,4,5,6,8],
  [3,4,5,6,9],
  [3,4,5,7,8],
  [3,4,5,7,9],
  [3,4,5,8,9],
  [3,4,6,7,8],
  [3,4,6,7,9],
  [3,4,6,8,9],
  [3,4,7,8,9],
  [3,5,6,7,8],
  [3,5,6,7,9],
  [3,5,6,8,9],
  [3,5,7,8,9],
  [3,6,7,8,9],
  [4,5,6,7,8],
  [4,5,6,7,9],
  [4,5,6,8,9],
  [4,5,7,8,9],
  [4,6,7,8,9],
  [5,6,7,8,9]]

theorem fiveGeometryChunk5_checked : ∀ g ∈ fiveGeometryChunk5, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk5, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase210
  · subst g
    exact fiveGeometryCase211
  · subst g
    exact fiveGeometryCase212
  · subst g
    exact fiveGeometryCase213
  · subst g
    exact fiveGeometryCase214
  · subst g
    exact fiveGeometryCase215
  · subst g
    exact fiveGeometryCase216
  · subst g
    exact fiveGeometryCase217
  · subst g
    exact fiveGeometryCase218
  · subst g
    exact fiveGeometryCase219
  · subst g
    exact fiveGeometryCase220
  · subst g
    exact fiveGeometryCase221
  · subst g
    exact fiveGeometryCase222
  · subst g
    exact fiveGeometryCase223
  · subst g
    exact fiveGeometryCase224
  · subst g
    exact fiveGeometryCase225
  · subst g
    exact fiveGeometryCase226
  · subst g
    exact fiveGeometryCase227
  · subst g
    exact fiveGeometryCase228
  · subst g
    exact fiveGeometryCase229
  · subst g
    exact fiveGeometryCase230
  · subst g
    exact fiveGeometryCase231
  · subst g
    exact fiveGeometryCase232
  · subst g
    exact fiveGeometryCase233
  · subst g
    exact fiveGeometryCase234
  · subst g
    exact fiveGeometryCase235
  · subst g
    exact fiveGeometryCase236
  · subst g
    exact fiveGeometryCase237
  · subst g
    exact fiveGeometryCase238
  · subst g
    exact fiveGeometryCase239
  · subst g
    exact fiveGeometryCase240
  · subst g
    exact fiveGeometryCase241
  · subst g
    exact fiveGeometryCase242
  · subst g
    exact fiveGeometryCase243
  · subst g
    exact fiveGeometryCase244
  · subst g
    exact fiveGeometryCase245
  · subst g
    exact fiveGeometryCase246
  · subst g
    exact fiveGeometryCase247
  · subst g
    exact fiveGeometryCase248
  · subst g
    exact fiveGeometryCase249
  · subst g
    exact fiveGeometryCase250
  · subst g
    exact fiveGeometryCase251

end LC004

import LC004.FiveClassGeometryCases0

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 42; shape: empty. -/
theorem fiveGeometrySpec042 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,6,9] (fiveOtherRanks [0,1,4,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase042 : FiveGeometryCase [0,1,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec042).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec042 x y).mp hxy)

/-- Exhaustive finite relation 43; shape: two_points. -/
theorem fiveGeometrySpec043 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,7,8] (fiveOtherRanks [0,1,4,7,8]) x y ↔ ((x = 0 ∧ y = 7) ∨ (x = 9 ∧ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase043 : FiveGeometryCase [0,1,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec043).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (0 : Fin 10) 9 (7 : Fin 10) 0
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 0 ∧ y = 7) ∨ (x = 9 ∧ y = 0)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec043 x y).mp hxy)

/-- Exhaustive finite relation 44; shape: rectangle. -/
theorem fiveGeometrySpec044 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,7,9] (fiveOtherRanks [0,1,4,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase044 : FiveGeometryCase [0,1,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec044).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec044 x y).mp hxy)

/-- Exhaustive finite relation 45; shape: rectangle. -/
theorem fiveGeometrySpec045 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,8,9] (fiveOtherRanks [0,1,4,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase045 : FiveGeometryCase [0,1,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec045).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec045 x y).mp hxy)

/-- Exhaustive finite relation 46; shape: fan. -/
theorem fiveGeometrySpec046 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,6,7] (fiveOtherRanks [0,1,5,6,7]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase046 : FiveGeometryCase [0,1,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec046).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 9)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec046 x y).mp hxy)

/-- Exhaustive finite relation 47; shape: empty. -/
theorem fiveGeometrySpec047 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,6,8] (fiveOtherRanks [0,1,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase047 : FiveGeometryCase [0,1,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec047).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec047 x y).mp hxy)

/-- Exhaustive finite relation 48; shape: fan. -/
theorem fiveGeometrySpec048 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,6,9] (fiveOtherRanks [0,1,5,6,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 7 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase048 : FiveGeometryCase [0,1,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec048).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (7 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨7, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 7 ∨ y = 9)) → x = 7 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec048 x y).mp hxy)

/-- Exhaustive finite relation 49; shape: rectangle. -/
theorem fiveGeometrySpec049 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,7,8] (fiveOtherRanks [0,1,5,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase049 : FiveGeometryCase [0,1,5,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec049).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec049 x y).mp hxy)

/-- Exhaustive finite relation 50; shape: empty. -/
theorem fiveGeometrySpec050 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,7,9] (fiveOtherRanks [0,1,5,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase050 : FiveGeometryCase [0,1,5,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec050).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec050 x y).mp hxy)

/-- Exhaustive finite relation 51; shape: rectangle. -/
theorem fiveGeometrySpec051 : ∀ x y : Fin 10,
    FiveCompatible [0,1,5,8,9] (fiveOtherRanks [0,1,5,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase051 : FiveGeometryCase [0,1,5,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec051).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec051 x y).mp hxy)

/-- Exhaustive finite relation 52; shape: rectangle. -/
theorem fiveGeometrySpec052 : ∀ x y : Fin 10,
    FiveCompatible [0,1,6,7,8] (fiveOtherRanks [0,1,6,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase052 : FiveGeometryCase [0,1,6,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec052).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec052 x y).mp hxy)

/-- Exhaustive finite relation 53; shape: rectangle. -/
theorem fiveGeometrySpec053 : ∀ x y : Fin 10,
    FiveCompatible [0,1,6,7,9] (fiveOtherRanks [0,1,6,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase053 : FiveGeometryCase [0,1,6,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec053).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨7, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 7 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec053 x y).mp hxy)

/-- Exhaustive finite relation 54; shape: empty. -/
theorem fiveGeometrySpec054 : ∀ x y : Fin 10,
    FiveCompatible [0,1,6,8,9] (fiveOtherRanks [0,1,6,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase054 : FiveGeometryCase [0,1,6,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec054).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec054 x y).mp hxy)

/-- Exhaustive finite relation 55; shape: rectangle. -/
theorem fiveGeometrySpec055 : ∀ x y : Fin 10,
    FiveCompatible [0,1,7,8,9] (fiveOtherRanks [0,1,7,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase055 : FiveGeometryCase [0,1,7,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec055).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [0,1,7,8,9] (fiveOtherRanks [0,1,7,8,9]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [0,1,7,8,9] (fiveOtherRanks [0,1,7,8,9])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 56; shape: empty. -/
theorem fiveGeometrySpec056 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,4,5] (fiveOtherRanks [0,2,3,4,5]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase056 : FiveGeometryCase [0,2,3,4,5] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec056).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec056 x y).mp hxy)

/-- Exhaustive finite relation 57; shape: rectangle. -/
theorem fiveGeometrySpec057 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,4,6] (fiveOtherRanks [0,2,3,4,6]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase057 : FiveGeometryCase [0,2,3,4,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec057).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec057 x y).mp hxy)

/-- Exhaustive finite relation 58; shape: rectangle. -/
theorem fiveGeometrySpec058 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,4,7] (fiveOtherRanks [0,2,3,4,7]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase058 : FiveGeometryCase [0,2,3,4,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec058).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec058 x y).mp hxy)

/-- Exhaustive finite relation 59; shape: empty. -/
theorem fiveGeometrySpec059 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,4,8] (fiveOtherRanks [0,2,3,4,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase059 : FiveGeometryCase [0,2,3,4,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec059).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec059 x y).mp hxy)

/-- Exhaustive finite relation 60; shape: rectangle. -/
theorem fiveGeometrySpec060 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,4,9] (fiveOtherRanks [0,2,3,4,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase060 : FiveGeometryCase [0,2,3,4,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec060).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨3, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 3 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec060 x y).mp hxy)

/-- Exhaustive finite relation 61; shape: rectangle. -/
theorem fiveGeometrySpec061 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,5,6] (fiveOtherRanks [0,2,3,5,6]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase061 : FiveGeometryCase [0,2,3,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec061).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec061 x y).mp hxy)

/-- Exhaustive finite relation 62; shape: empty. -/
theorem fiveGeometrySpec062 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,5,7] (fiveOtherRanks [0,2,3,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase062 : FiveGeometryCase [0,2,3,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec062).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec062 x y).mp hxy)

/-- Exhaustive finite relation 63; shape: empty. -/
theorem fiveGeometrySpec063 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,5,8] (fiveOtherRanks [0,2,3,5,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase063 : FiveGeometryCase [0,2,3,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec063).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec063 x y).mp hxy)

/-- Exhaustive finite relation 64; shape: rectangle. -/
theorem fiveGeometrySpec064 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,5,9] (fiveOtherRanks [0,2,3,5,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase064 : FiveGeometryCase [0,2,3,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec064).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec064 x y).mp hxy)

/-- Exhaustive finite relation 65; shape: rectangle. -/
theorem fiveGeometrySpec065 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,6,7] (fiveOtherRanks [0,2,3,6,7]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase065 : FiveGeometryCase [0,2,3,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec065).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec065 x y).mp hxy)

/-- Exhaustive finite relation 66; shape: empty. -/
theorem fiveGeometrySpec066 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,6,8] (fiveOtherRanks [0,2,3,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase066 : FiveGeometryCase [0,2,3,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec066).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec066 x y).mp hxy)

/-- Exhaustive finite relation 67; shape: two_points. -/
theorem fiveGeometrySpec067 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,6,9] (fiveOtherRanks [0,2,3,6,9]) x y ↔ ((x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase067 : FiveGeometryCase [0,2,3,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec067).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (3 : Fin 10) 4 (4 : Fin 10) 9
  · intro _
    refine ⟨3, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 9)) → x = 3 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec067 x y).mp hxy)

/-- Exhaustive finite relation 68; shape: empty. -/
theorem fiveGeometrySpec068 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,7,8] (fiveOtherRanks [0,2,3,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase068 : FiveGeometryCase [0,2,3,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec068).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec068 x y).mp hxy)

/-- Exhaustive finite relation 69; shape: rectangle. -/
theorem fiveGeometrySpec069 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,7,9] (fiveOtherRanks [0,2,3,7,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase069 : FiveGeometryCase [0,2,3,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec069).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec069 x y).mp hxy)

/-- Exhaustive finite relation 70; shape: rectangle. -/
theorem fiveGeometrySpec070 : ∀ x y : Fin 10,
    FiveCompatible [0,2,3,8,9] (fiveOtherRanks [0,2,3,8,9]) x y ↔ (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase070 : FiveGeometryCase [0,2,3,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec070).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([4] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨4, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([4] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 4 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec070 x y).mp hxy)

/-- Exhaustive finite relation 71; shape: empty. -/
theorem fiveGeometrySpec071 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,5,6] (fiveOtherRanks [0,2,4,5,6]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase071 : FiveGeometryCase [0,2,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec071).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec071 x y).mp hxy)

/-- Exhaustive finite relation 72; shape: empty. -/
theorem fiveGeometrySpec072 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,5,7] (fiveOtherRanks [0,2,4,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase072 : FiveGeometryCase [0,2,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec072).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec072 x y).mp hxy)

/-- Exhaustive finite relation 73; shape: empty. -/
theorem fiveGeometrySpec073 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,5,8] (fiveOtherRanks [0,2,4,5,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase073 : FiveGeometryCase [0,2,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec073).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec073 x y).mp hxy)

/-- Exhaustive finite relation 74; shape: empty. -/
theorem fiveGeometrySpec074 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,5,9] (fiveOtherRanks [0,2,4,5,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase074 : FiveGeometryCase [0,2,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec074).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec074 x y).mp hxy)

/-- Exhaustive finite relation 75; shape: empty. -/
theorem fiveGeometrySpec075 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,6,7] (fiveOtherRanks [0,2,4,6,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase075 : FiveGeometryCase [0,2,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec075).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec075 x y).mp hxy)

/-- Exhaustive finite relation 76; shape: empty. -/
theorem fiveGeometrySpec076 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,6,8] (fiveOtherRanks [0,2,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase076 : FiveGeometryCase [0,2,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec076).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec076 x y).mp hxy)

/-- Exhaustive finite relation 77; shape: empty. -/
theorem fiveGeometrySpec077 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,6,9] (fiveOtherRanks [0,2,4,6,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase077 : FiveGeometryCase [0,2,4,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec077).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec077 x y).mp hxy)

/-- Exhaustive finite relation 78; shape: empty. -/
theorem fiveGeometrySpec078 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,7,8] (fiveOtherRanks [0,2,4,7,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase078 : FiveGeometryCase [0,2,4,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec078).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec078 x y).mp hxy)

/-- Exhaustive finite relation 79; shape: empty. -/
theorem fiveGeometrySpec079 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,7,9] (fiveOtherRanks [0,2,4,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase079 : FiveGeometryCase [0,2,4,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec079).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec079 x y).mp hxy)

/-- Exhaustive finite relation 80; shape: empty. -/
theorem fiveGeometrySpec080 : ∀ x y : Fin 10,
    FiveCompatible [0,2,4,8,9] (fiveOtherRanks [0,2,4,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase080 : FiveGeometryCase [0,2,4,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec080).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec080 x y).mp hxy)

/-- Exhaustive finite relation 81; shape: empty. -/
theorem fiveGeometrySpec081 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,6,7] (fiveOtherRanks [0,2,5,6,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase081 : FiveGeometryCase [0,2,5,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec081).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec081 x y).mp hxy)

/-- Exhaustive finite relation 82; shape: empty. -/
theorem fiveGeometrySpec082 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,6,8] (fiveOtherRanks [0,2,5,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase082 : FiveGeometryCase [0,2,5,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec082).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec082 x y).mp hxy)

/-- Exhaustive finite relation 83; shape: rectangle. -/
theorem fiveGeometrySpec083 : ∀ x y : Fin 10,
    FiveCompatible [0,2,5,6,9] (fiveOtherRanks [0,2,5,6,9]) x y ↔ (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase083 : FiveGeometryCase [0,2,5,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec083).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([3] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([3] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec083 x y).mp hxy)

def fiveGeometryChunk1 : List (List Nat) :=
  [[0,1,4,6,9],
  [0,1,4,7,8],
  [0,1,4,7,9],
  [0,1,4,8,9],
  [0,1,5,6,7],
  [0,1,5,6,8],
  [0,1,5,6,9],
  [0,1,5,7,8],
  [0,1,5,7,9],
  [0,1,5,8,9],
  [0,1,6,7,8],
  [0,1,6,7,9],
  [0,1,6,8,9],
  [0,1,7,8,9],
  [0,2,3,4,5],
  [0,2,3,4,6],
  [0,2,3,4,7],
  [0,2,3,4,8],
  [0,2,3,4,9],
  [0,2,3,5,6],
  [0,2,3,5,7],
  [0,2,3,5,8],
  [0,2,3,5,9],
  [0,2,3,6,7],
  [0,2,3,6,8],
  [0,2,3,6,9],
  [0,2,3,7,8],
  [0,2,3,7,9],
  [0,2,3,8,9],
  [0,2,4,5,6],
  [0,2,4,5,7],
  [0,2,4,5,8],
  [0,2,4,5,9],
  [0,2,4,6,7],
  [0,2,4,6,8],
  [0,2,4,6,9],
  [0,2,4,7,8],
  [0,2,4,7,9],
  [0,2,4,8,9],
  [0,2,5,6,7],
  [0,2,5,6,8],
  [0,2,5,6,9]]

theorem fiveGeometryChunk1_checked : ∀ g ∈ fiveGeometryChunk1, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk1, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase042
  · subst g
    exact fiveGeometryCase043
  · subst g
    exact fiveGeometryCase044
  · subst g
    exact fiveGeometryCase045
  · subst g
    exact fiveGeometryCase046
  · subst g
    exact fiveGeometryCase047
  · subst g
    exact fiveGeometryCase048
  · subst g
    exact fiveGeometryCase049
  · subst g
    exact fiveGeometryCase050
  · subst g
    exact fiveGeometryCase051
  · subst g
    exact fiveGeometryCase052
  · subst g
    exact fiveGeometryCase053
  · subst g
    exact fiveGeometryCase054
  · subst g
    exact fiveGeometryCase055
  · subst g
    exact fiveGeometryCase056
  · subst g
    exact fiveGeometryCase057
  · subst g
    exact fiveGeometryCase058
  · subst g
    exact fiveGeometryCase059
  · subst g
    exact fiveGeometryCase060
  · subst g
    exact fiveGeometryCase061
  · subst g
    exact fiveGeometryCase062
  · subst g
    exact fiveGeometryCase063
  · subst g
    exact fiveGeometryCase064
  · subst g
    exact fiveGeometryCase065
  · subst g
    exact fiveGeometryCase066
  · subst g
    exact fiveGeometryCase067
  · subst g
    exact fiveGeometryCase068
  · subst g
    exact fiveGeometryCase069
  · subst g
    exact fiveGeometryCase070
  · subst g
    exact fiveGeometryCase071
  · subst g
    exact fiveGeometryCase072
  · subst g
    exact fiveGeometryCase073
  · subst g
    exact fiveGeometryCase074
  · subst g
    exact fiveGeometryCase075
  · subst g
    exact fiveGeometryCase076
  · subst g
    exact fiveGeometryCase077
  · subst g
    exact fiveGeometryCase078
  · subst g
    exact fiveGeometryCase079
  · subst g
    exact fiveGeometryCase080
  · subst g
    exact fiveGeometryCase081
  · subst g
    exact fiveGeometryCase082
  · subst g
    exact fiveGeometryCase083

end LC004

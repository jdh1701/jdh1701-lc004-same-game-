import LC004.FiveClassFiniteGeometry

set_option Elab.async false

namespace LC004

/-- Exhaustive finite relation 0; shape: rectangle. -/
theorem fiveGeometrySpec000 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,4] (fiveOtherRanks [0,1,2,3,4]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase000 : FiveGeometryCase [0,1,2,3,4] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec000).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [0,1,2,3,4] (fiveOtherRanks [0,1,2,3,4]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [0,1,2,3,4] (fiveOtherRanks [0,1,2,3,4])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 1; shape: empty. -/
theorem fiveGeometrySpec001 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,5] (fiveOtherRanks [0,1,2,3,5]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase001 : FiveGeometryCase [0,1,2,3,5] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec001).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec001 x y).mp hxy)

/-- Exhaustive finite relation 2; shape: rectangle. -/
theorem fiveGeometrySpec002 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,6] (fiveOtherRanks [0,1,2,3,6]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase002 : FiveGeometryCase [0,1,2,3,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec002).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec002 x y).mp hxy)

/-- Exhaustive finite relation 3; shape: rectangle. -/
theorem fiveGeometrySpec003 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,7] (fiveOtherRanks [0,1,2,3,7]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase003 : FiveGeometryCase [0,1,2,3,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec003).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec003 x y).mp hxy)

/-- Exhaustive finite relation 4; shape: empty. -/
theorem fiveGeometrySpec004 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,8] (fiveOtherRanks [0,1,2,3,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase004 : FiveGeometryCase [0,1,2,3,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec004).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec004 x y).mp hxy)

/-- Exhaustive finite relation 5; shape: rectangle. -/
theorem fiveGeometrySpec005 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,3,9] (fiveOtherRanks [0,1,2,3,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase005 : FiveGeometryCase [0,1,2,3,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec005).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [0,1,2,3,9] (fiveOtherRanks [0,1,2,3,9]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [0,1,2,3,9] (fiveOtherRanks [0,1,2,3,9])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 6; shape: rectangle. -/
theorem fiveGeometrySpec006 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,4,5] (fiveOtherRanks [0,1,2,4,5]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase006 : FiveGeometryCase [0,1,2,4,5] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec006).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec006 x y).mp hxy)

/-- Exhaustive finite relation 7; shape: empty. -/
theorem fiveGeometrySpec007 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,4,6] (fiveOtherRanks [0,1,2,4,6]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase007 : FiveGeometryCase [0,1,2,4,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec007).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec007 x y).mp hxy)

/-- Exhaustive finite relation 8; shape: rectangle. -/
theorem fiveGeometrySpec008 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,4,7] (fiveOtherRanks [0,1,2,4,7]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase008 : FiveGeometryCase [0,1,2,4,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec008).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec008 x y).mp hxy)

/-- Exhaustive finite relation 9; shape: rectangle. -/
theorem fiveGeometrySpec009 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,4,8] (fiveOtherRanks [0,1,2,4,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase009 : FiveGeometryCase [0,1,2,4,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec009).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec009 x y).mp hxy)

/-- Exhaustive finite relation 10; shape: empty. -/
theorem fiveGeometrySpec010 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,4,9] (fiveOtherRanks [0,1,2,4,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase010 : FiveGeometryCase [0,1,2,4,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec010).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec010 x y).mp hxy)

/-- Exhaustive finite relation 11; shape: fan. -/
theorem fiveGeometrySpec011 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,5,6] (fiveOtherRanks [0,1,2,5,6]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase011 : FiveGeometryCase [0,1,2,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec011).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 0)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec011 x y).mp hxy)

/-- Exhaustive finite relation 12; shape: empty. -/
theorem fiveGeometrySpec012 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,5,7] (fiveOtherRanks [0,1,2,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase012 : FiveGeometryCase [0,1,2,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec012).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec012 x y).mp hxy)

/-- Exhaustive finite relation 13; shape: rectangle. -/
theorem fiveGeometrySpec013 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,5,8] (fiveOtherRanks [0,1,2,5,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase013 : FiveGeometryCase [0,1,2,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec013).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 7, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 7 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec013 x y).mp hxy)

/-- Exhaustive finite relation 14; shape: rectangle. -/
theorem fiveGeometrySpec014 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,5,9] (fiveOtherRanks [0,1,2,5,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase014 : FiveGeometryCase [0,1,2,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec014).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec014 x y).mp hxy)

/-- Exhaustive finite relation 15; shape: fan. -/
theorem fiveGeometrySpec015 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,6,7] (fiveOtherRanks [0,1,2,6,7]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase015 : FiveGeometryCase [0,1,2,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec015).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (9 : Fin 10) (9 : Fin 10))
  · intro _
    refine ⟨9, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 9 ∨ y = 9)) → x = 9 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec015 x y).mp hxy)

/-- Exhaustive finite relation 16; shape: empty. -/
theorem fiveGeometrySpec016 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,6,8] (fiveOtherRanks [0,1,2,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase016 : FiveGeometryCase [0,1,2,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec016).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec016 x y).mp hxy)

/-- Exhaustive finite relation 17; shape: rectangle. -/
theorem fiveGeometrySpec017 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,6,9] (fiveOtherRanks [0,1,2,6,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase017 : FiveGeometryCase [0,1,2,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec017).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec017 x y).mp hxy)

/-- Exhaustive finite relation 18; shape: rectangle. -/
theorem fiveGeometrySpec018 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,7,8] (fiveOtherRanks [0,1,2,7,8]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase018 : FiveGeometryCase [0,1,2,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec018).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨9, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 9 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec018 x y).mp hxy)

/-- Exhaustive finite relation 19; shape: empty. -/
theorem fiveGeometrySpec019 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,7,9] (fiveOtherRanks [0,1,2,7,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase019 : FiveGeometryCase [0,1,2,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec019).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec019 x y).mp hxy)

/-- Exhaustive finite relation 20; shape: rectangle. -/
theorem fiveGeometrySpec020 : ∀ x y : Fin 10,
    FiveCompatible [0,1,2,8,9] (fiveOtherRanks [0,1,2,8,9]) x y ↔ (x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase020 : FiveGeometryCase [0,1,2,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec020).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro hc
    have hn : finiteBlockCross [0,1,2,8,9] (fiveOtherRanks [0,1,2,8,9]) = false := by decide +kernel
    have ht := (finiteBlockCross_iff [0,1,2,8,9] (fiveOtherRanks [0,1,2,8,9])).mpr hc
    rw [hn] at ht
    contradiction

/-- Exhaustive finite relation 21; shape: rectangle. -/
theorem fiveGeometrySpec021 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,4,5] (fiveOtherRanks [0,1,3,4,5]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase021 : FiveGeometryCase [0,1,3,4,5] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec021).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec021 x y).mp hxy)

/-- Exhaustive finite relation 22; shape: rectangle. -/
theorem fiveGeometrySpec022 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,4,6] (fiveOtherRanks [0,1,3,4,6]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase022 : FiveGeometryCase [0,1,3,4,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec022).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec022 x y).mp hxy)

/-- Exhaustive finite relation 23; shape: two_points. -/
theorem fiveGeometrySpec023 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,4,7] (fiveOtherRanks [0,1,3,4,7]) x y ↔ ((x = 0 ∧ y = 4) ∨ (x = 7 ∧ y = 9)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase023 : FiveGeometryCase [0,1,3,4,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec023).mpr ?_, ?_⟩
  · exact choiceRelationClosed_twoPoints (0 : Fin 10) 7 (4 : Fin 10) 9
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, ((x = 0 ∧ y = 4) ∨ (x = 7 ∧ y = 9)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec023 x y).mp hxy)

/-- Exhaustive finite relation 24; shape: rectangle. -/
theorem fiveGeometrySpec024 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,4,8] (fiveOtherRanks [0,1,3,4,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase024 : FiveGeometryCase [0,1,3,4,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec024).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec024 x y).mp hxy)

/-- Exhaustive finite relation 25; shape: rectangle. -/
theorem fiveGeometrySpec025 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,4,9] (fiveOtherRanks [0,1,3,4,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase025 : FiveGeometryCase [0,1,3,4,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec025).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))
  · intro _
    refine ⟨7, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) → x = 7 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec025 x y).mp hxy)

/-- Exhaustive finite relation 26; shape: empty. -/
theorem fiveGeometrySpec026 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,5,6] (fiveOtherRanks [0,1,3,5,6]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase026 : FiveGeometryCase [0,1,3,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec026).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec026 x y).mp hxy)

/-- Exhaustive finite relation 27; shape: empty. -/
theorem fiveGeometrySpec027 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,5,7] (fiveOtherRanks [0,1,3,5,7]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase027 : FiveGeometryCase [0,1,3,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec027).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec027 x y).mp hxy)

/-- Exhaustive finite relation 28; shape: empty. -/
theorem fiveGeometrySpec028 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,5,8] (fiveOtherRanks [0,1,3,5,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase028 : FiveGeometryCase [0,1,3,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec028).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec028 x y).mp hxy)

/-- Exhaustive finite relation 29; shape: empty. -/
theorem fiveGeometrySpec029 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,5,9] (fiveOtherRanks [0,1,3,5,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase029 : FiveGeometryCase [0,1,3,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec029).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec029 x y).mp hxy)

/-- Exhaustive finite relation 30; shape: rectangle. -/
theorem fiveGeometrySpec030 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,6,7] (fiveOtherRanks [0,1,3,6,7]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase030 : FiveGeometryCase [0,1,3,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec030).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec030 x y).mp hxy)

/-- Exhaustive finite relation 31; shape: empty. -/
theorem fiveGeometrySpec031 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,6,8] (fiveOtherRanks [0,1,3,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase031 : FiveGeometryCase [0,1,3,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec031).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec031 x y).mp hxy)

/-- Exhaustive finite relation 32; shape: rectangle. -/
theorem fiveGeometrySpec032 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,6,9] (fiveOtherRanks [0,1,3,6,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([4] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase032 : FiveGeometryCase [0,1,3,6,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec032).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([4] : List Nat))
  · intro _
    refine ⟨0, 4, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([4] : List Nat)) → x = 0 ∨ y = 4 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec032 x y).mp hxy)

/-- Exhaustive finite relation 33; shape: rectangle. -/
theorem fiveGeometrySpec033 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,7,8] (fiveOtherRanks [0,1,3,7,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase033 : FiveGeometryCase [0,1,3,7,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec033).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec033 x y).mp hxy)

/-- Exhaustive finite relation 34; shape: rectangle. -/
theorem fiveGeometrySpec034 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,7,9] (fiveOtherRanks [0,1,3,7,9]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([3] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase034 : FiveGeometryCase [0,1,3,7,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec034).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([3] : List Nat))
  · intro _
    refine ⟨0, 3, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([3] : List Nat)) → x = 0 ∨ y = 3 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec034 x y).mp hxy)

/-- Exhaustive finite relation 35; shape: empty. -/
theorem fiveGeometrySpec035 : ∀ x y : Fin 10,
    FiveCompatible [0,1,3,8,9] (fiveOtherRanks [0,1,3,8,9]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase035 : FiveGeometryCase [0,1,3,8,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec035).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec035 x y).mp hxy)

/-- Exhaustive finite relation 36; shape: fan. -/
theorem fiveGeometrySpec036 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,5,6] (fiveOtherRanks [0,1,4,5,6]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase036 : FiveGeometryCase [0,1,4,5,6] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec036).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (0 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 0 ∨ y = 0)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec036 x y).mp hxy)

/-- Exhaustive finite relation 37; shape: rectangle. -/
theorem fiveGeometrySpec037 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,5,7] (fiveOtherRanks [0,1,4,5,7]) x y ↔ (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase037 : FiveGeometryCase [0,1,4,5,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec037).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([7] : List Nat)) (fun y : Fin 10 => y.val ∈ ([9] : List Nat))
  · intro _
    refine ⟨0, 9, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([7] : List Nat) ∧ y.val ∈ ([9] : List Nat)) → x = 0 ∨ y = 9 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec037 x y).mp hxy)

/-- Exhaustive finite relation 38; shape: rectangle. -/
theorem fiveGeometrySpec038 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,5,8] (fiveOtherRanks [0,1,4,5,8]) x y ↔ (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase038 : FiveGeometryCase [0,1,4,5,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec038).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0] : List Nat)) (fun y : Fin 10 => y.val ∈ ([7] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([0] : List Nat) ∧ y.val ∈ ([7] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec038 x y).mp hxy)

/-- Exhaustive finite relation 39; shape: fan. -/
theorem fiveGeometrySpec039 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,5,9] (fiveOtherRanks [0,1,4,5,9]) x y ↔ ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 7 ∨ y = 0)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase039 : FiveGeometryCase [0,1,4,5,9] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec039).mpr ?_, ?_⟩
  · exact choiceRelationClosed_inter (choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([0,3,4,7,9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0,3,4,7,9] : List Nat))) (choiceRelationClosed_fan (7 : Fin 10) (0 : Fin 10))
  · intro _
    refine ⟨7, 0, ?_⟩
    have h : ∀ x y : Fin 10, ((x.val ∈ ([0,3,4,7,9] : List Nat) ∧ y.val ∈ ([0,3,4,7,9] : List Nat)) ∧ (x = 7 ∨ y = 0)) → x = 7 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec039 x y).mp hxy)

/-- Exhaustive finite relation 40; shape: rectangle. -/
theorem fiveGeometrySpec040 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,6,7] (fiveOtherRanks [0,1,4,6,7]) x y ↔ (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase040 : FiveGeometryCase [0,1,4,6,7] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec040).mpr ?_, ?_⟩
  · exact choiceRelationClosed_rectangle (fun x : Fin 10 => x.val ∈ ([9] : List Nat)) (fun y : Fin 10 => y.val ∈ ([0] : List Nat))
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, (x.val ∈ ([9] : List Nat) ∧ y.val ∈ ([0] : List Nat)) → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec040 x y).mp hxy)

/-- Exhaustive finite relation 41; shape: empty. -/
theorem fiveGeometrySpec041 : ∀ x y : Fin 10,
    FiveCompatible [0,1,4,6,8] (fiveOtherRanks [0,1,4,6,8]) x y ↔ False := by
  apply finiteRelationMatches_sound
  decide +kernel

theorem fiveGeometryCase041 : FiveGeometryCase [0,1,4,6,8] := by
  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec041).mpr ?_, ?_⟩
  · exact choiceRelationClosed_empty
  · intro _
    refine ⟨0, 0, ?_⟩
    have h : ∀ x y : Fin 10, False → x = 0 ∨ y = 0 := by decide +kernel
    intro x y hxy
    exact h x y ((fiveGeometrySpec041 x y).mp hxy)

def fiveGeometryChunk0 : List (List Nat) :=
  [[0,1,2,3,4],
  [0,1,2,3,5],
  [0,1,2,3,6],
  [0,1,2,3,7],
  [0,1,2,3,8],
  [0,1,2,3,9],
  [0,1,2,4,5],
  [0,1,2,4,6],
  [0,1,2,4,7],
  [0,1,2,4,8],
  [0,1,2,4,9],
  [0,1,2,5,6],
  [0,1,2,5,7],
  [0,1,2,5,8],
  [0,1,2,5,9],
  [0,1,2,6,7],
  [0,1,2,6,8],
  [0,1,2,6,9],
  [0,1,2,7,8],
  [0,1,2,7,9],
  [0,1,2,8,9],
  [0,1,3,4,5],
  [0,1,3,4,6],
  [0,1,3,4,7],
  [0,1,3,4,8],
  [0,1,3,4,9],
  [0,1,3,5,6],
  [0,1,3,5,7],
  [0,1,3,5,8],
  [0,1,3,5,9],
  [0,1,3,6,7],
  [0,1,3,6,8],
  [0,1,3,6,9],
  [0,1,3,7,8],
  [0,1,3,7,9],
  [0,1,3,8,9],
  [0,1,4,5,6],
  [0,1,4,5,7],
  [0,1,4,5,8],
  [0,1,4,5,9],
  [0,1,4,6,7],
  [0,1,4,6,8]]

theorem fiveGeometryChunk0_checked : ∀ g ∈ fiveGeometryChunk0, FiveGeometryCase g := by
  intro g hg
  simp only [fiveGeometryChunk0, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41
  · subst g
    exact fiveGeometryCase000
  · subst g
    exact fiveGeometryCase001
  · subst g
    exact fiveGeometryCase002
  · subst g
    exact fiveGeometryCase003
  · subst g
    exact fiveGeometryCase004
  · subst g
    exact fiveGeometryCase005
  · subst g
    exact fiveGeometryCase006
  · subst g
    exact fiveGeometryCase007
  · subst g
    exact fiveGeometryCase008
  · subst g
    exact fiveGeometryCase009
  · subst g
    exact fiveGeometryCase010
  · subst g
    exact fiveGeometryCase011
  · subst g
    exact fiveGeometryCase012
  · subst g
    exact fiveGeometryCase013
  · subst g
    exact fiveGeometryCase014
  · subst g
    exact fiveGeometryCase015
  · subst g
    exact fiveGeometryCase016
  · subst g
    exact fiveGeometryCase017
  · subst g
    exact fiveGeometryCase018
  · subst g
    exact fiveGeometryCase019
  · subst g
    exact fiveGeometryCase020
  · subst g
    exact fiveGeometryCase021
  · subst g
    exact fiveGeometryCase022
  · subst g
    exact fiveGeometryCase023
  · subst g
    exact fiveGeometryCase024
  · subst g
    exact fiveGeometryCase025
  · subst g
    exact fiveGeometryCase026
  · subst g
    exact fiveGeometryCase027
  · subst g
    exact fiveGeometryCase028
  · subst g
    exact fiveGeometryCase029
  · subst g
    exact fiveGeometryCase030
  · subst g
    exact fiveGeometryCase031
  · subst g
    exact fiveGeometryCase032
  · subst g
    exact fiveGeometryCase033
  · subst g
    exact fiveGeometryCase034
  · subst g
    exact fiveGeometryCase035
  · subst g
    exact fiveGeometryCase036
  · subst g
    exact fiveGeometryCase037
  · subst g
    exact fiveGeometryCase038
  · subst g
    exact fiveGeometryCase039
  · subst g
    exact fiveGeometryCase040
  · subst g
    exact fiveGeometryCase041

end LC004

import LC004.FourGapCoefficientSupport

namespace LC004
open scoped Classical

def fourGapCode {n : Nat} (a b c d x : Fin n) : Nat :=
  if x = a ∨ x = b ∨ x = c ∨ x = d then 0 else
  if x < a ∨ d < x then 4 else if x < b then 1 else if x < c then 2 else 3

def fourGapPattern {n : Nat} (a b c d : Fin n) : ColorPattern n :=
  Setoid.ker (fourGapCode a b c d)

theorem fourGapPattern_gaps {n : Nat} {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∀ S ∈ [pairInterior a b,pairInterior b c,pairInterior c d,pairExterior a d],
      ∀ x ∈ S, ∀ y ∈ S, fourGapPattern a b c d x y := by
  intro S hS x hx y hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hS
  change fourGapCode a b c d x = fourGapCode a b c d y
  rcases hS with rfl | rfl | rfl | rfl <;>
    simp only [pairInterior,pairExterior,Finset.mem_filter,Finset.mem_univ,true_and] at hx hy <;>
    unfold fourGapCode <;> split_ifs <;> omega

set_option maxHeartbeats 0 in
theorem fourGapPattern_separates_crossing {n : Nat} {a b c d u v x y : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hu : u = a ∨ u = b ∨ u = c ∨ u = d)
    (hv : v = a ∨ v = b ∨ v = c ∨ v = d)
    (hcross : (u < x ∧ x < v ∧ v < y) ∨ (x < u ∧ u < y ∧ y < v))
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d)
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) (hyd : y ≠ d) :
    ¬ fourGapPattern a b c d x y := by
  intro he
  change fourGapCode a b c d x = fourGapCode a b c d y at he
  simp only [fourGapCode,hxa,hxb,hxc,hxd,hya,hyb,hyc,hyd,false_or,ite_false] at he
  rcases hcross with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;>
    rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    split_ifs at he <;> omega

/-- A crossed four-occurrence class forces its collected signed join
coefficient to vanish. The crossing chord may use any two of its occurrences. -/
theorem winningJoinCoefficient_crossed_four_zero {n : Nat} (p : ColorPattern n)
    {a b c d u v x y : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hclass : patternClassPositions p a = {a,b,c,d})
    (hau : p a u) (hav : p a v) (hxy : p x y) (hnax : ¬ p a x)
    (hcross : (u < x ∧ x < v ∧ v < y) ∨ (x < u ∧ u < y ∧ y < v)) :
    winningJoinCoefficient n p = 0 := by
  have mem (z : Fin n) (hz : p a z) : z = a ∨ z = b ∨ z = c ∨ z = d := by
    have hm : z ∈ patternClassPositions p a := by simpa [patternClassPositions] using hz
    rw [hclass] at hm
    simpa using hm
  have hpa (z : Fin n) (hz : z ∈ ({a,b,c,d} : Finset (Fin n))) : p a z := by
    have hm : z ∈ patternClassPositions p a := hclass.symm ▸ hz
    simpa [patternClassPositions] using hm
  have hnay : ¬ p a y := fun h => hnax (p.trans h (p.symm hxy))
  have hx (z : Fin n) (hz : z ∈ ({a,b,c,d} : Finset (Fin n))) : x ≠ z := by
    intro h
    exact hnax (h.symm ▸ hpa z hz)
  have hy (z : Fin n) (hz : z ∈ ({a,b,c,d} : Finset (Fin n))) : y ≠ z := by
    intro h
    exact hnay (h.symm ▸ hpa z hz)
  apply winningJoinCoefficient_zero_of_four_gap_separator p (fourGapPattern a b c d)
    hab hbc hcd hclass
  · change fourGapCode a b c d a = fourGapCode a b c d b
    simp [fourGapCode]
  · change fourGapCode a b c d a = fourGapCode a b c d c
    simp [fourGapCode]
  · change fourGapCode a b c d a = fourGapCode a b c d d
    simp [fourGapCode]
  · exact fourGapPattern_gaps hab hbc hcd
  · intro hle
    exact fourGapPattern_separates_crossing hab hbc hcd (mem u hau) (mem v hav)
      hcross (hx a (by simp)) (hx b (by simp)) (hx c (by simp)) (hx d (by simp))
      (hy a (by simp)) (hy b (by simp)) (hy c (by simp)) (hy d (by simp)) (hle hxy)

#print axioms fourGapPattern_gaps
#print axioms fourGapPattern_separates_crossing
#print axioms winningJoinCoefficient_crossed_four_zero
end LC004

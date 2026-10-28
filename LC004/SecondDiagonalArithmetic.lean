import LC004.MatchingCatalan

namespace LC004

/-- The Catalan representation coefficient, expressed without division.
This is an arithmetic identity, independent of either refined count. -/
theorem second_diagonal_representation_coefficient (k : Nat) (hk : 1 ≤ k) :
    2 * ((k + 1).choose 2 * catalan (k + 1)) =
      (k + 3) * (2 * k + 2).choose (k - 1) := by
  have htri := Nat.choose_succ_right_eq (k + 1) 1
  simp only [Nat.choose_one_right, Nat.add_sub_cancel] at htri
  have hcat : (k + 2) * catalan (k + 1) =
      (2 * k + 2).choose (k + 1) := by
    simpa only [Nat.centralBinom, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
      succ_mul_catalan_eq_centralBinom (k + 1)
  have h₁ : (2 * k + 2).choose (k + 1) * (k + 1) =
      (2 * k + 2).choose k * (k + 2) := by
    have h := Nat.choose_succ_right_eq (2 * k + 2) k
    have hs : 2 * k + 2 - k = k + 2 := by omega
    simpa only [hs] using h
  have h₂ : (2 * k + 2).choose k * k =
      (2 * k + 2).choose (k - 1) * (k + 3) := by
    have h := Nat.choose_succ_right_eq (2 * k + 2) (k - 1)
    have hs : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have ht : 2 * k + 2 - (k - 1) = k + 3 := by omega
    simpa only [hs, ht] using h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 2 by omega)
  calc
    (k + 2) * (2 * ((k + 1).choose 2 * catalan (k + 1))) =
        ((k + 1).choose 2 * 2) * ((k + 2) * catalan (k + 1)) := by ring
    _ = ((k + 1) * k) * (2 * k + 2).choose (k + 1) := by rw [htri, hcat]
    _ = k * ((2 * k + 2).choose (k + 1) * (k + 1)) := by ring
    _ = k * ((2 * k + 2).choose k * (k + 2)) := by rw [h₁]
    _ = ((2 * k + 2).choose k * k) * (k + 2) := by ring
    _ = ((2 * k + 2).choose (k - 1) * (k + 3)) * (k + 2) := by rw [h₂]
    _ = (k + 2) * ((k + 3) * (2 * k + 2).choose (k - 1)) := by ring

/-- Handles the natural-number subtraction in the count reduction.
The two displayed numerical identities are explicit hypotheses. -/
theorem second_diagonal_subtraction_algebra (k R D T : Nat) (hk : 1 ≤ k)
    (hR : 2 * R = (k + 3) * D) (hT : 2 * T = (k - 1) * D) :
    R - D + T = k * D := by
  have hle : D ≤ R := by nlinarith
  have hsub := Nat.sub_add_cancel hle
  have hkd : (k - 1) * D + D = k * D := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      congrArg (fun j : Nat => j * D) (Nat.sub_add_cancel hk)
  nlinarith

/-- Conditional assembly of the proposed formula. This does not assert
or assume as axioms the two outstanding refined cardinality evaluations. -/
theorem second_diagonal_formula_of_refined_counts (k : Nat) (hk : 2 ≤ k)
    (hfour : fourfoldNoncrossingPatternCount (2 * k + 2) =
      (2 * k + 2).choose (k - 1))
    (htriple : 2 * twoTripleNoncrossingPatternCount (2 * k + 2) =
      (k - 1) * (2 * k + 2).choose (k - 1)) :
    winningColorPatternCount (2 * k + 2) k =
      k * (2 * k + 2).choose (k - 1) := by
  rw [second_diagonal_count_reduction_catalan, hfour]
  exact second_diagonal_subtraction_algebra k _ _ _ (by omega)
    (second_diagonal_representation_coefficient k (by omega)) htriple

#print axioms second_diagonal_representation_coefficient
#print axioms second_diagonal_subtraction_algebra
#print axioms second_diagonal_formula_of_refined_counts

end LC004

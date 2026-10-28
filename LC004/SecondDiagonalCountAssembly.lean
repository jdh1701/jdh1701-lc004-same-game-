import LC004.IntrinsicDiagonalProfiles

namespace LC004

theorem second_diagonal_pattern_predicate (k : Nat) (p : ColorPattern (2 * k + 2)) :
    (WinningColorPattern p ∧ colorPatternClassCount p = k) ↔
      (WinningColorPattern p ∧ FourfoldPairPattern p) ∨
      (WinningColorPattern p ∧ TwoTriplePairPattern p) := by
  constructor
  · rintro ⟨hw, hk⟩
    have hlen : 2 * k + 2 = 2 * colorPatternClassCount p + 2 := by rw [hk]
    rcases winning_intrinsic_second_diagonal_profiles p hw hlen with hf | ht
    · exact Or.inl ⟨hw, hf⟩
    · exact Or.inr ⟨hw, ht⟩
  · rintro (⟨hw, hf⟩ | ⟨hw, ht⟩)
    · have h := fourfold_profile_position_count p hf
      exact ⟨hw, by omega⟩
    · have h := two_triple_profile_position_count p ht
      exact ⟨hw, by omega⟩

/-- The target count is exactly the disjoint sum of the two intrinsic
profile counts, with no missing color-class-count side conditions. -/
theorem second_diagonal_winning_count_split (k : Nat) :
    winningColorPatternCount (2 * k + 2) k =
      fourfoldWinningPatternCount (2 * k + 2) + twoTripleWinningPatternCount (2 * k + 2) := by
  classical
  let f := fun p : ColorPattern (2 * k + 2) => WinningColorPattern p ∧ FourfoldPairPattern p
  let t := fun p : ColorPattern (2 * k + 2) => WinningColorPattern p ∧ TwoTriplePairPattern p
  have hd : Disjoint f t := by
    apply disjoint_iff_inf_le.mpr
    intro p h
    exact intrinsic_diagonal_profiles_disjoint p h.1.2 h.2.2
  calc
    _ = Fintype.card {p : ColorPattern (2 * k + 2) // f p ∨ t p} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (second_diagonal_pattern_predicate k))
    _ = Fintype.card {p // f p} + Fintype.card {p // t p} :=
      Fintype.card_subtype_or_disjoint f t hd
    _ = _ := rfl

/-- Complete reduction of the actual Same Game target count to three
pure noncrossing partition counts. No closed cardinalities are assumed. -/
theorem second_diagonal_count_reduction (k : Nat) :
    winningColorPatternCount (2 * k + 2) k =
      ((k + 1).choose 2 * noncrossingPairPatternCount (2 * k + 2) -
        fourfoldNoncrossingPatternCount (2 * k + 2)) +
          twoTripleNoncrossingPatternCount (2 * k + 2) := by
  rw [second_diagonal_winning_count_split, fourfold_second_diagonal_count_reduction,
    two_triple_winning_count_eq_noncrossing]

#print axioms second_diagonal_winning_count_split
#print axioms second_diagonal_count_reduction

end LC004

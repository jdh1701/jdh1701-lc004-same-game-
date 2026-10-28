import LC004.FourBlockCrossing

namespace LC004

/-- An external forced pair is compatible with BOTH allowable
noncrossing internal pairings of a four-occurrence color precisely
when it does not cross the original four-point color block. -/
theorem both_pairings_compatible_iff_block_noncrossing
    {u v a b c d : Nat}
    (huv : u < v) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hu : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    (¬ PairCross u v a b ∧ ¬ PairCross u v c d ∧
     ¬ PairCross u v a d ∧ ¬ PairCross u v b c) ↔
      ¬ FourBlockCross u v a b c d := by
  rw [four_block_cross_iff_pair_cross huv hab hbc hcd hu hv]
  tauto

end LC004

import Mathlib

namespace LC004

/-- Two disjoint pairs with their endpoints ordered increasingly
cross exactly when their endpoints alternate. -/
def PairCross (u v x y : Nat) : Prop :=
  (u < x ∧ x < v ∧ v < y) ∨
  (x < u ∧ u < y ∧ y < v)

/-- A pair crosses the four-point block if some block position lies
strictly inside the pair while another lies strictly outside. -/
def FourBlockCross (u v a b c d : Nat) : Prop :=
  ((u < a ∧ a < v) ∨ (u < b ∧ b < v) ∨
   (u < c ∧ c < v) ∨ (u < d ∧ d < v)) ∧
  ((a < u ∨ v < a) ∨ (b < u ∨ v < b) ∨
   (c < u ∨ v < c) ∨ (d < u ∨ v < d))

/-- The two noncrossing perfect matchings on a<b<c<d
are (a,b)(c,d) and (a,d)(b,c). A disjoint other-color pair
crosses the original four-block iff it crosses an edge of at
least one of these two matchings. -/
theorem four_block_cross_iff_pair_cross
    {u v a b c d : Nat}
    (huv : u < v) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hu : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    FourBlockCross u v a b c d ↔
      PairCross u v a b ∨ PairCross u v c d ∨
      PairCross u v a d ∨ PairCross u v b c := by
  unfold FourBlockCross PairCross
  omega

end LC004

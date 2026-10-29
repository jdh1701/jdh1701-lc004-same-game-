import LC004.NoncrossingProfileEnumeration
import LC004.DoubleExceptionalWordCount
import LC004.SecondDiagonalArithmetic
import LC004.SecondDiagonalEndpoint

namespace LC004
open scoped BigOperators

open scoped Classical in
theorem two_triple_noncrossing_count_closed (k : Nat) (hk : 2 ≤ k) :
    2 * twoTripleNoncrossingPatternCount (2 * k + 2) =
      (k - 1) * (2 * k + 2).choose (k - 1) := by
  classical
  let P : CyclicDegreeWord (2 * k + 2) → Prop := fun w =>
    (∑ i, (w i).val = 2 * k + 2) ∧ DoubleExceptionalWord w 3
  have hrotate : ∀ w r, P (rotateDegreeWord w r) ↔ P w := by
    intro w r
    exact and_congr (by rw [degreeWord_sum_rotate]) (doubleExceptionalWord_rotate w 3 r)
  have hmark := marked_rooted_word_card P (fun _ h => h.1) hrotate 3 2
    (fun w h => doubleExceptionalWord_arity_card w 3 (by omega) h.2)
  have heq := Fintype.card_congr (noncrossingProfileWordEquiv (2 * k + 2)
    TwoTriplePairPattern (fun w => DoubleExceptionalWord w 3) twoTriple_iff_doubleExceptionalWord)
  change twoTripleNoncrossingPatternCount (2 * k + 2) =
    Fintype.card {w : CyclicDegreeWord (2 * k + 2) // P w ∧ RootedDegreeWord w} at heq
  rw [heq, ← hmark, double_anchored_word_count k hk]
  have h := Nat.succ_mul_choose_eq (2 * k + 1) (k - 2)
  have hs : k - 2 + 1 = k - 1 := by omega
  simpa only [Nat.succ_eq_add_one, hs, Nat.mul_comm] using h

/-- The complete second-diagonal formula for winning color patterns,
with maximal-run deletion semantics inherited from the certified reduction. -/
theorem winningColorPatternCount_second_diagonal (k : Nat) (hk : 1 ≤ k) :
    winningColorPatternCount (2 * k + 2) k = k * (2 * k + 2).choose (k - 1) := by
  by_cases h : k = 1
  · subst k
    exact second_diagonal_formula_at_one
  · exact second_diagonal_formula_of_refined_counts k hk
      (fourfold_noncrossing_count_closed k hk)
      (two_triple_noncrossing_count_closed k (by omega))

#print axioms two_triple_noncrossing_count_closed
#print axioms winningColorPatternCount_second_diagonal

end LC004

import LC004.DoubleFiberCountCorrespondence

namespace LC004
open scoped BigOperators

/-- A generic finite combination count, applied below to the matching's
unlabeled quotient classes rather than any ordering of its edges. -/
theorem fixed_card_finset_count {α : Type*} [Fintype α] (k : Nat) :
    Nat.card {s : Finset α // s.card = k} = (Fintype.card α).choose k := by
  classical
  let e : {s : Finset α // s.card = k} ≃
      {s : Finset α // s ∈ (Finset.univ : Finset α).powersetCard k} :=
    Equiv.subtypeEquivRight (fun s => by simp only [Finset.mem_powersetCard,
      Finset.subset_univ, true_and])
  calc
    _ = Nat.card {s : Finset α // s ∈ (Finset.univ : Finset α).powersetCard k} := Nat.card_congr e
    _ = ((Finset.univ : Finset α).powersetCard k).card := Nat.card_eq_finsetCard _
    _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ]

/-- Every position lies in exactly one two-position matching class. -/
theorem pair_pattern_position_count {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) : n = 2 * colorPatternClassCount p := by
  classical
  have h := selected_pair_positions_card p hp (Finset.univ : Finset (Quotient p))
  have hs : selectedPatternPositions p (Finset.univ : Finset (Quotient p)) =
      (Finset.univ : Finset (Fin n)) := by
    ext i
    simp [selectedPatternPositions]
  simp only [hs, Finset.card_univ, Fintype.card_fin] at h
  simpa only [colorPatternClassCount, Nat.card_eq_fintype_card] using h

theorem pair_pattern_even_class_count (m : Nat) (p : ColorPattern (2 * m))
    (hp : NoncrossingPairPattern p) : colorPatternClassCount p = m := by
  have h := pair_pattern_position_count p hp
  omega

/-- For 2m positions, the representation count is the matching count
multiplied by the unordered choice of two of its m edges. The matching
count itself has not been replaced by a Catalan formula here. -/
theorem fourfold_matching_representation_count (m : Nat) :
    fourfoldMatchingRepresentationCount (2 * m) =
      m.choose 2 * noncrossingPairPatternCount (2 * m) := by
  classical
  unfold fourfoldMatchingRepresentationCount
  change Fintype.card
    ((p : {p : ColorPattern (2 * m) // NoncrossingPairPattern p}) ×
      {chosen : Finset (Quotient p.val) // chosen.card = 2}) = _
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _p : {p : ColorPattern (2 * m) // NoncrossingPairPattern p}, m.choose 2 := by
      apply Finset.sum_congr rfl
      intro p _
      have hchoose := fixed_card_finset_count (α := Quotient p.val) 2
      have hclasses := pair_pattern_even_class_count m p.val p.property
      simp only [colorPatternClassCount, Nat.card_eq_fintype_card] at hclasses
      simpa only [Nat.card_eq_fintype_card, hclasses] using hchoose
    _ = _ := by simp [noncrossingPairPatternCount, Nat.mul_comm]

theorem fourfold_representation_count_second_diagonal (k : Nat) :
    fourfoldMatchingRepresentationCount (2 * k + 2) =
      (k + 1).choose 2 * noncrossingPairPatternCount (2 * k + 2) := by
  have h := fourfold_matching_representation_count (k + 1)
  simpa only [Nat.mul_add, Nat.mul_one] using h

/-- All representation and duplicate factors are now proved for the
actual spaces. The remaining terms are pure noncrossing partition counts. -/
theorem fourfold_second_diagonal_count_reduction (k : Nat) :
    fourfoldWinningPatternCount (2 * k + 2) =
      (k + 1).choose 2 * noncrossingPairPatternCount (2 * k + 2) -
        fourfoldNoncrossingPatternCount (2 * k + 2) := by
  rw [fourfold_winning_count_eq_representations_sub_noncrossing,
    fourfold_representation_count_second_diagonal]

#print axioms pair_pattern_position_count
#print axioms fourfold_matching_representation_count
#print axioms fourfold_second_diagonal_count_reduction

end LC004

import LC004.SmallPatternCorrespondence

namespace LC004

/-- Exactly two distinct three-position classes, with pairs elsewhere. -/
def TwoTriplePairPattern {n : Nat} (p : ColorPattern n) : Prop :=
  ∃ a b, ¬ p a b ∧ (patternClassPositions p a).card = 3 ∧
    (patternClassPositions p b).card = 3 ∧
    ∀ i, ¬ p a i → ¬ p b i → (patternClassPositions p i).card = 2

theorem two_triple_profile_small_classes {n : Nat} (p : ColorPattern n)
    (hp : TwoTriplePairPattern p) :
    ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3 := by
  classical
  obtain ⟨a, b, _, ha, hb, hrest⟩ := hp
  intro i
  by_cases hai : p a i
  · right
    rw [← pattern_class_eq_of_related p hai]
    exact ha
  · by_cases hbi : p b i
    · right
      rw [← pattern_class_eq_of_related p hbi]
      exact hb
    · exact Or.inl (hrest i hai hbi)

theorem winning_two_triple_iff_noncrossing {n : Nat} (p : ColorPattern n)
    (hp : TwoTriplePairPattern p) : WinningColorPattern p ↔ PatternNoncrossing p :=
  winning_small_pattern_iff_noncrossing p (two_triple_profile_small_classes p hp)

/-- Identity on underlying position partitions: no color-label factor,
block ordering, or certificate multiplicity enters this correspondence. -/
def twoTripleWinningPatternEquiv (n : Nat) :
    {p : ColorPattern n // WinningColorPattern p ∧ TwoTriplePairPattern p} ≃
    {p : ColorPattern n // PatternNoncrossing p ∧ TwoTriplePairPattern p} where
  toFun p := ⟨p.val, (winning_two_triple_iff_noncrossing p.val p.property.2).mp p.property.1,
    p.property.2⟩
  invFun p := ⟨p.val, (winning_two_triple_iff_noncrossing p.val p.property.2).mpr p.property.1,
    p.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def twoTripleWinningPatternCount (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n // WinningColorPattern p ∧ TwoTriplePairPattern p}

noncomputable def twoTripleNoncrossingPatternCount (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n // PatternNoncrossing p ∧ TwoTriplePairPattern p}

theorem two_triple_winning_count_eq_noncrossing (n : Nat) :
    twoTripleWinningPatternCount n = twoTripleNoncrossingPatternCount n := by
  classical
  exact Fintype.card_congr (twoTripleWinningPatternEquiv n)

#print axioms winning_two_triple_iff_noncrossing
#print axioms two_triple_winning_count_eq_noncrossing

end LC004

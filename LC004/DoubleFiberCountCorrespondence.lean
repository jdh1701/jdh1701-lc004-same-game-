import LC004.DoubleFiberGeometry

namespace LC004

theorem noncrossing_fourfold_winning {n : Nat} (p : ColorPattern n)
    (hp : FourfoldPairPattern p) (hnc : PatternNoncrossing p) : WinningColorPattern p := by
  classical
  have hdbl := (fourfold_double_fiber_iff_noncrossing p hp).mpr hnc
  have hpos : 0 < (fourfoldRepresentationFiber p).card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  have hrp : fourfoldRepresentationPattern r = p := (Finset.mem_filter.mp hr).2
  exact hrp ▸ fourfold_representation_winning r

/-- Identity on the underlying coarse partition. Winning is automatic
for a conventional noncrossing fourfold-plus-pairs pattern. -/
def doubleFiberNoncrossingPatternEquiv (n : Nat) :
    {w : {p : ColorPattern n // WinningColorPattern p ∧ FourfoldPairPattern p} //
      (fourfoldRepresentationFiber w.val).card = 2} ≃
    {p : ColorPattern n // PatternNoncrossing p ∧ FourfoldPairPattern p} where
  toFun w := ⟨w.val.val,
    (fourfold_double_fiber_iff_noncrossing w.val.val w.val.property.2).mp w.property,
    w.val.property.2⟩
  invFun p := ⟨⟨p.val, noncrossing_fourfold_winning p.val p.property.2 p.property.1,
    p.property.2⟩, (fourfold_double_fiber_iff_noncrossing p.val p.property.2).mpr p.property.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def fourfoldNoncrossingPatternCount (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n // PatternNoncrossing p ∧ FourfoldPairPattern p}

theorem fourfold_double_count_eq_noncrossing (n : Nat) :
    fourfoldDoublePatternCount n = fourfoldNoncrossingPatternCount n := by
  classical
  calc
    _ = Fintype.card {w : {p : ColorPattern n // WinningColorPattern p ∧ FourfoldPairPattern p} //
        (fourfoldRepresentationFiber w.val).card = 2} := by
      simp only [fourfoldDoublePatternCount, Fintype.card_subtype]
    _ = _ := Fintype.card_congr (doubleFiberNoncrossingPatternEquiv n)

/-- Concrete fourfold count reduction. Both terms on the right are now
finite partition/matching spaces, with no unproved fiber assumptions. -/
theorem fourfold_winning_count_eq_representations_sub_noncrossing (n : Nat) :
    fourfoldWinningPatternCount n = fourfoldMatchingRepresentationCount n -
      fourfoldNoncrossingPatternCount n := by
  rw [fourfold_winning_count_subtraction, fourfold_double_count_eq_noncrossing]

#print axioms fourfold_double_count_eq_noncrossing
#print axioms fourfold_winning_count_eq_representations_sub_noncrossing

end LC004

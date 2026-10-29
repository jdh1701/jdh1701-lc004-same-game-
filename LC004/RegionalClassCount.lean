import LC004.NoncrossingCoefficientProduct

namespace LC004
open scoped BigOperators Classical

/-- Send a local equivalence class to the global class containing it. -/
noncomputable def regionalQuotientMap {n : Nat} (p pi : ColorPattern n) :
    (Σ q : Quotient pi, Quotient (restrictColorPattern p (patternRegionEmbed pi q))) → Quotient p :=
  fun x => Quotient.lift (fun i => Quotient.mk p (patternRegionEmbed pi x.1 i))
    (fun _ _ h => Quotient.sound ((restrictColorPattern_rel _ _ _ _).mp h)) x.2

theorem regionalQuotientMap_bijective {n : Nat} (p pi : ColorPattern n) (hp : p ≤ pi) :
    Function.Bijective (regionalQuotientMap p pi) := by
  constructor
  · rintro ⟨q,x⟩ ⟨r,y⟩ h
    induction x using Quotient.inductionOn with | h i =>
      induction y using Quotient.inductionOn with | h j =>
        have hab : p (patternRegionEmbed pi q i) (patternRegionEmbed pi r j) := Quotient.exact h
        have hqr : q = r := (patternRegionEmbed_class pi q i).symm.trans
          ((Quotient.sound (hp hab)).trans (patternRegionEmbed_class pi r j))
        subst r
        have hij : Quotient.mk (restrictColorPattern p (patternRegionEmbed pi q)) i =
            Quotient.mk (restrictColorPattern p (patternRegionEmbed pi q)) j :=
          Quotient.sound ((restrictColorPattern_rel _ _ _ _).mpr hab)
        exact congrArg (Sigma.mk q) hij
  · intro x
    induction x using Quotient.inductionOn with | h a =>
      obtain ⟨q,i,rfl⟩ := patternRegionEmbed_cover pi a
      exact ⟨⟨q,Quotient.mk _ i⟩,rfl⟩

noncomputable def regionalQuotientEquiv {n : Nat} (p pi : ColorPattern n) (hp : p ≤ pi) :
    (Σ q : Quotient pi, Quotient (restrictColorPattern p (patternRegionEmbed pi q))) ≃ Quotient p :=
  Equiv.ofBijective _ (regionalQuotientMap_bijective p pi hp)

/-- Class counts add over every coarsening, including the empty pattern. -/
theorem pattern_class_count_regions {n : Nat} (p pi : ColorPattern n) (hp : p ≤ pi) :
    Nat.card (Quotient p) = ∑ q : Quotient pi,
      Nat.card (Quotient (restrictColorPattern p (patternRegionEmbed pi q))) := by
  rw [← Nat.card_congr (regionalQuotientEquiv p pi hp), Nat.card_sigma]

theorem pattern_class_weight_regions {n : Nat} (p pi : ColorPattern n) (hp : p ≤ pi) (b : Int) :
    b ^ Nat.card (Quotient p) = ∏ q : Quotient pi,
      b ^ Nat.card (Quotient (restrictColorPattern p (patternRegionEmbed pi q))) := by
  rw [pattern_class_count_regions p pi hp, ← Finset.prod_pow_eq_pow_sum]

/-- The signed coefficient with its alphabet-size weight factors locally. -/
theorem weighted_winningJoinCoefficient_regions {n : Nat} (p pi : ColorPattern n)
    (hp : p ≤ pi) (hnc : PatternNoncrossing pi) (b : Int) :
    winningJoinCoefficient n p * b ^ Nat.card (Quotient p) =
      ∏ q : Quotient pi,
        (winningJoinCoefficient (patternQuotientFiber pi q).card
          (restrictColorPattern p (patternRegionEmbed pi q)) *
        b ^ Nat.card (Quotient (restrictColorPattern p (patternRegionEmbed pi q)))) := by
  rw [winningJoinCoefficient_noncrossing_product p pi hp hnc,
    pattern_class_weight_regions p pi hp, Finset.prod_mul_distrib]

#print axioms regionalQuotientEquiv
#print axioms pattern_class_count_regions
#print axioms weighted_winningJoinCoefficient_regions
end LC004

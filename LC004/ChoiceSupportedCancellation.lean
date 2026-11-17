import LC004.ChoiceSupportedDomains

namespace LC004
open scoped Classical

/-- Every proper cut is crossed by a compatibility cover on actual solutions.
Unlike mere nonuniversality, such a cover survives removal of unused values
when neither coordinate is constant. -/
def ChoiceCoveredCuts {ι : Type*} {D : ι → Type*} (A : Finset (∀ i, D i)) : Prop :=
  ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
    ∃ i ∈ S, ∃ j ∉ S, ∃ x : D i, ∃ y : D j, ∀ a ∈ A, a i = x ∨ a j = y

theorem choiceSupport_exists_ne {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (i : ι) (p : D i)
    (hnc : ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i) :
    ∃ x : ChoiceSupport A i, x.val ≠ p := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  by_cases hap : a i = p
  · exact ⟨⟨b i, b, hb, rfl⟩, fun hbp => hab (hap.trans hbp.symm)⟩
  · exact ⟨⟨a i, a, ha, rfl⟩, hap⟩

theorem choiceSupportedFamily_connected_of_covers {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (hnc : ∀ i, ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i)
    (hcuts : ChoiceCoveredCuts A) : ChoiceCoordinatesConnected (choiceSupportedFamily A) := by
  intro S hS hSc
  obtain ⟨i, hi, j, hj, p, q, hcover⟩ := hcuts S hS hSc
  obtain ⟨x, hx⟩ := choiceSupport_exists_ne A i p (hnc i)
  obtain ⟨y, hy⟩ := choiceSupport_exists_ne A j q (hnc j)
  refine ⟨i, hi, j, hj, ?_⟩
  intro hall
  obtain ⟨a, ha, hai, haj⟩ := (choiceSupportedFamily_pair A i j x y).mp (hall x y)
  rcases hcover a ha with hp | hq
  · exact hx (hai.symm.trans hp)
  · exact hy (haj.symm.trans hq)

theorem choiceCoveredCuts_small_edge {ι : Type*} {D : ι → Type*}
    [Nontrivial ι] (A : Finset (∀ i, D i)) (hcuts : ChoiceCoveredCuts A) :
    ChoiceSmallEdge A := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨u, hu, v, hv, p, q, hcover⟩ := hcuts {i} ⟨i, rfl⟩ ⟨j, Ne.symm hij⟩
  exact ⟨u, v, fun h => hv (h ▸ hu), p, q, hcover⟩

theorem choiceSupportedFamily_small_edge {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] (A : Finset (∀ i, D i))
    (hnc : ∀ i, ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i)
    (hedge : ChoiceSmallEdge A) : ChoiceSmallEdge (choiceSupportedFamily A) := by
  obtain ⟨i, j, hij, p, q, hcover⟩ := hedge
  obtain ⟨x, hx⟩ := choiceSupport_exists_ne A i p (hnc i)
  obtain ⟨y, hy⟩ := choiceSupport_exists_ne A j q (hnc j)
  have hp : ∃ a ∈ A, a i = p := by
    obtain ⟨a, ha, haj⟩ := y.property
    exact ⟨a, ha, (hcover a ha).resolve_right (fun h => hy (haj.symm.trans h))⟩
  have hq : ∃ a ∈ A, a j = q := by
    obtain ⟨a, ha, hai⟩ := x.property
    exact ⟨a, ha, (hcover a ha).resolve_left (fun h => hx (hai.symm.trans h))⟩
  refine ⟨i, j, hij, ⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  intro b hb
  rcases hcover _ ((mem_choiceSupportedFamily A b).mp hb) with hi | hj
  · exact Or.inl (Subtype.ext hi)
  · exact Or.inr (Subtype.ext hj)

theorem choiceAlternatingSum_zero_of_nonconstant_covered_cuts {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nontrivial ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i))
    (hnc : ∀ i, ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i)
    (hclosed : ChoiceSolutionsClosed A) (hbinary : ChoiceBinaryDetermined A)
    (hcuts : ChoiceCoveredCuts A) (hthree : 3 ≤ A.card) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  letI : ∀ i, Nontrivial (ChoiceSupport A i) := fun i => choiceSupport_nontrivial A i (hnc i)
  rw [choiceAlternatingSum_supported A]
  have hc : @ChoiceSolutionsClosed ι (ChoiceSupport A)
      (fun i => Classical.decEq (ChoiceSupport A i)) (choiceSupportedFamily A) :=
    (choiceSolutionsClosed_decidableEq (choiceSupportedFamily A) _ _).mp
      (choiceSupportedFamily_closed A hclosed)
  have ht : 3 ≤ (choiceSupportedFamily A).card := by
    simpa only [choiceSupportedFamily_card] using hthree
  have hz := choiceAlternatingSum_zero_of_three (choiceSupportedFamily A)
    (choiceSupportedFamily_support A) hc (choiceSupportedFamily_binary A hbinary)
    (choiceSupportedFamily_connected_of_covers A hnc hcuts) ht
    (choiceSupportedFamily_small_edge A hnc (choiceCoveredCuts_small_edge A hcuts))
  let d₁ : DecidableEq (Sigma (ChoiceSupport A)) := inferInstance
  let d₂ : DecidableEq (Sigma (ChoiceSupport A)) :=
    @Sigma.instDecidableEqSigma ι (ChoiceSupport A)
      (Classical.decEq ι) (fun i => Classical.decEq (ChoiceSupport A i))
  exact (facetAlternatingSum_decidableEq (choiceFacets (choiceSupportedFamily A)) d₁ d₂).trans hz

/-- No full-support or nonconstant-coordinate hypothesis remains: constant
coordinates give a cone, and the nonconstant case is normalized to support. -/
theorem choiceAlternatingSum_zero_of_covered_cuts {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nontrivial ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hclosed : ChoiceSolutionsClosed A)
    (hbinary : ChoiceBinaryDetermined A) (hcuts : ChoiceCoveredCuts A)
    (hthree : 3 ≤ A.card) : faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  by_cases hnc : ∀ i, ∃ a ∈ A, ∃ b ∈ A, a i ≠ b i
  · exact choiceAlternatingSum_zero_of_nonconstant_covered_cuts A hnc hclosed hbinary hcuts hthree
  · push_neg at hnc
    obtain ⟨i, hi⟩ := hnc
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hne
    apply choiceAlternatingSum_zero_of_constant A i (a i)
    intro b hb
    exact hi b hb a ha

theorem choiceCoveredCuts_of_binary_spec {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hcut : ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
      ∃ i ∈ S, ∃ j ∉ S, ∃ p : D i, ∃ q : D j,
        ∀ x y, C i j x y → x = p ∨ y = q) : ChoiceCoveredCuts A := by
  intro S hS hSc
  obtain ⟨i, hi, j, hj, p, q, hc⟩ := hcut S hS hSc
  refine ⟨i, hi, j, hj, p, q, ?_⟩
  intro a ha
  exact hc _ _ ((hspec a).mp ha i j (fun h => hj (h ▸ hi)))

/-- Local geometric input form with unsupported values and constant coordinates
handled internally. The remaining caller obligations are a binary specification,
local majority closure and row/column-cover edges crossing all proper cuts. -/
theorem choiceAlternatingSum_zero_of_covered_binary_spec {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nontrivial ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hCclosed : ∀ i j, i ≠ j → ChoiceRelationClosed (C i j))
    (hcut : ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
      ∃ i ∈ S, ∃ j ∉ S, ∃ p : D i, ∃ q : D j,
        ∀ x y, C i j x y → x = p ∨ y = q)
    (hthree : 3 ≤ A.card) : faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  obtain ⟨hclosed, hbinary⟩ := choiceSolutionsClosed_and_binaryDetermined_of_binary_spec A C hspec hCclosed
  exact choiceAlternatingSum_zero_of_covered_cuts A hclosed hbinary
    (choiceCoveredCuts_of_binary_spec A C hspec hcut) hthree

/-- Three solutions on ambient three-value domains; value 2 is unused. This
checks that the final theorem really traverses support restriction. -/
def ambientThreeChoiceFan : Finset (Fin 2 → Fin 3) :=
  Finset.univ.filter (fun a => a 0 < 2 ∧ a 1 < 2 ∧ (a 0 = 0 ∨ a 1 = 0))

theorem ambientThreeChoiceFan_card : ambientThreeChoiceFan.card = 3 := by decide

theorem ambientThreeChoiceFan_uses_no_two :
    ∀ a ∈ ambientThreeChoiceFan, ∀ i, a i ≠ 2 := by decide

theorem ambientThreeChoiceFan_cancellation :
    letI : DecidableEq (Fin 2) := Classical.decEq _
    letI : DecidableEq (Fin 3) := Classical.decEq _
    faceAlternatingSum (facetFaces (choiceFacets ambientThreeChoiceFan)) = 0 := by
  have hb : ChoiceBinaryDetermined ambientThreeChoiceFan := by
    unfold ChoiceBinaryDetermined ChoicePairProjection
    decide
  have he : ∀ i j : Fin 2, i ≠ j → ∀ a ∈ ambientThreeChoiceFan,
      a i = 0 ∨ a j = 0 := by decide
  have hcuts : ChoiceCoveredCuts ambientThreeChoiceFan := by
    intro S hS hSc
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hSc
    exact ⟨i, hi, j, hj, 0, 0, he i j (fun h => hj (h ▸ hi))⟩
  letI : DecidableEq (Fin 2) := Classical.decEq _
  letI : DecidableEq (Fin 3) := Classical.decEq _
  apply choiceAlternatingSum_zero_of_covered_cuts ambientThreeChoiceFan ?_ hb hcuts (by decide)
  intro a ha b hb c hc
  simp only [ambientThreeChoiceFan, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc ⊢
  refine ⟨?_, ?_, twoFan_closed_choiceMajority 0 0 (a 0) (b 0) (c 0)
    (a 1) (b 1) (c 1) ha.2.2 hb.2.2 hc.2.2⟩
  · unfold choiceMajority
    split_ifs
    · exact hb.1
    · exact ha.1
  · unfold choiceMajority
    split_ifs
    · exact hb.2.1
    · exact ha.2.1

#print axioms choiceSupportedFamily_connected_of_covers
#print axioms choiceAlternatingSum_zero_of_covered_cuts
#print axioms choiceAlternatingSum_zero_of_covered_binary_spec
#print axioms ambientThreeChoiceFan_cancellation
end LC004

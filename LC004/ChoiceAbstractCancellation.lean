import LC004.ChoiceQuotientFaceSum
import LC004.ChoiceBinaryClosure

namespace LC004
open scoped Classical

/-- One local compatibility relation lies in a union of a row and a column.
Two-fans and matchings of size at most two have this property. -/
def ChoiceSmallEdge {ι : Type*} {D : ι → Type*} (A : Finset (∀ i, D i)) : Prop :=
  ∃ i j, i ≠ j ∧ ∃ x : D i, ∃ y : D j, ∀ a ∈ A, a i = x ∨ a j = y

theorem choiceQuotient_nontrivial_of_three {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hthree : 3 ≤ A.card) (hsmall : ChoiceSmallEdge A) :
    Nontrivial (ChoiceCoordinateQuotient A hsupport) := by
  classical
  by_contra hn
  haveI : Subsingleton (ChoiceCoordinateQuotient A hsupport) :=
    not_nontrivial_iff_subsingleton.mp hn
  have hbij : ∀ i j, ChoiceRelationBijective (ChoicePairProjection A i j) := by
    intro i j
    exact @Quotient.exact ι (choiceBijectiveSetoid A hsupport) i j (Subsingleton.elim _ _)
  have hcard : ∀ i x, (choiceValueFiber A i x).card ≤ 1 := by
    intro i x
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, hai⟩ := (mem_choiceValueFiber A i x a).mp ha
    obtain ⟨hb, hbi⟩ := (mem_choiceValueFiber A i x b).mp hb
    funext j
    exact ((choicePair_bijective_iff_determines A hsupport i j).mp (hbij i j)).1
      a ha b hb (hai.trans hbi.symm)
  obtain ⟨i, j, _, x, y, hxy⟩ := hsmall
  have hsub : A ⊆ choiceValueFiber A i x ∪ choiceValueFiber A j y := by
    intro a ha
    rcases hxy a ha with hi | hj
    · exact Finset.mem_union_left _ ((mem_choiceValueFiber A i x a).mpr ⟨ha, hi⟩)
    · exact Finset.mem_union_right _ ((mem_choiceValueFiber A j y a).mpr ⟨ha, hj⟩)
  have hc : A.card ≤ 2 := calc
    A.card ≤ (choiceValueFiber A i x ∪ choiceValueFiber A j y).card := Finset.card_le_card hsub
    _ ≤ (choiceValueFiber A i x).card + (choiceValueFiber A j y).card := Finset.card_union_le _ _
    _ ≤ 2 := by have hi := hcard i x; have hj := hcard j y; omega
  omega

/-- Abstract cancellation including the global bijective-coordinate reduction
and the one-component boundary case. Original-game geometry is not assumed. -/
theorem choiceAlternatingSum_zero_of_three {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hclosed : ChoiceSolutionsClosed A) (hbinary : ChoiceBinaryDetermined A)
    (hconn : ChoiceCoordinatesConnected A) (hthree : 3 ≤ A.card)
    (hsmall : ChoiceSmallEdge A) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  letI := choiceQuotient_nontrivial_of_three A hsupport hthree hsmall
  exact choiceAlternatingSum_zero_of_nontrivial_quotient A hsupport hclosed hbinary hconn

theorem choiceAlternatingSum_zero_of_constant {ι : Type*} {D : ι → Type*}
    [Fintype ι] (A : Finset (∀ i, D i)) (i : ι) (x : D i)
    (hconstant : ∀ a ∈ A, a i = x) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  classical
  apply faceAlternatingSum_zero_of_cone _ (Sigma.mk i x)
  · intro s hs
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces _ _).mp hs
    exact (mem_facetFaces _ _).mpr ⟨f, hf, (Finset.erase_subset _ _).trans hsf⟩
  · intro s hs
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces _ _).mp hs
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
    exact (mem_facetFaces _ _).mpr ⟨_, (mem_choiceFacets A _).mpr ⟨a, ha, rfl⟩,
      Finset.insert_subset ((mem_choiceFacet a i x).mpr (hconstant a ha)) hsf⟩

/-- The usable binary-specification form, incorporating Claude's independently
contributed closure lemma instead of assuming global closure without a bridge. -/
theorem choiceAlternatingSum_zero_of_binary_spec {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hCclosed : ∀ i j, i ≠ j → ChoiceRelationClosed (C i j))
    (hconn : ChoiceCoordinatesConnected A) (hthree : 3 ≤ A.card)
    (hsmall : ChoiceSmallEdge A) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  obtain ⟨hclosed, hbinary⟩ :=
    choiceSolutionsClosed_and_binaryDetermined_of_binary_spec A C hspec hCclosed
  exact choiceAlternatingSum_zero_of_three A hsupport hclosed hbinary hconn hthree hsmall

theorem choiceCoordinatesConnected_of_binary_spec {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hconn : ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
      ∃ i ∈ S, ∃ j ∉ S, ¬ ∀ x y, C i j x y) : ChoiceCoordinatesConnected A := by
  intro S hS hSc
  obtain ⟨i, hi, j, hj, hn⟩ := hconn S hS hSc
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  refine ⟨i, hi, j, hj, ?_⟩
  intro hall
  apply hn
  intro x y
  obtain ⟨a, ha, hai, haj⟩ := hall x y
  simpa [hai, haj] using (hspec a).mp ha i j hij

/-- Direct input form for geometric compatibility tables: local closure,
connectedness of the raw constraints, and one covered edge imply cancellation.
No global closure, exact-projection connectedness, or quotient hypotheses are
left for the caller to postulate. Supported domains remain explicit. -/
theorem choiceAlternatingSum_zero_of_local_constraints {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ a, a ∈ A ↔ ∀ i j, i ≠ j → C i j (a i) (a j))
    (hCclosed : ∀ i j, i ≠ j → ChoiceRelationClosed (C i j))
    (hCconn : ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
      ∃ i ∈ S, ∃ j ∉ S, ¬ ∀ x y, C i j x y)
    (hthree : 3 ≤ A.card)
    (hedge : ∃ i j, i ≠ j ∧ ∃ x : D i, ∃ y : D j,
      ∀ u v, C i j u v → u = x ∨ v = y) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  apply choiceAlternatingSum_zero_of_binary_spec A hsupport C hspec hCclosed
    (choiceCoordinatesConnected_of_binary_spec A C hspec hCconn) hthree
  obtain ⟨i, j, hij, x, y, he⟩ := hedge
  refine ⟨i, j, hij, x, y, ?_⟩
  intro a ha
  exact he (a i) (a j) ((hspec a).mp ha i j hij)

/-- An actual three-solution system satisfies the complete abstract theorem,
including connectedness and the small-edge boundary hypothesis. -/
theorem binaryChoiceFan_abstract_cancellation :
    letI : DecidableEq (Fin 2) := Classical.decEq _
    faceAlternatingSum (facetFaces (choiceFacets binaryChoiceFan)) = 0 := by
  have hs : ∀ i x, ∃ a ∈ binaryChoiceFan, a i = x := by decide
  have hb : ChoiceBinaryDetermined binaryChoiceFan := by
    unfold ChoiceBinaryDetermined ChoicePairProjection
    decide
  have hn : ∀ i j : Fin 2, i ≠ j →
      ¬ ∀ x y, ChoicePairProjection binaryChoiceFan i j x y := by
    unfold ChoicePairProjection
    decide
  have hc : ChoiceCoordinatesConnected binaryChoiceFan := by
    intro S hS hSc
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hSc
    exact ⟨i, hi, j, hj, hn i j (fun h => hj (h ▸ hi))⟩
  have he : ChoiceSmallEdge binaryChoiceFan := by
    refine ⟨0, 1, by decide, 0, 0, ?_⟩
    intro a ha
    simpa [binaryChoiceFan] using ha
  letI : DecidableEq (Fin 2) := Classical.decEq _
  apply choiceAlternatingSum_zero_of_three binaryChoiceFan hs ?_ hb hc (by decide) he
  intro a ha b hb c hc
  simp only [binaryChoiceFan, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc ⊢
  exact twoFan_closed_choiceMajority 0 0 (a 0) (b 0) (c 0) (a 1) (b 1) (c 1) ha hb hc

#print axioms choiceQuotient_nontrivial_of_three
#print axioms choiceAlternatingSum_zero_of_three
#print axioms choiceAlternatingSum_zero_of_constant
#print axioms choiceAlternatingSum_zero_of_binary_spec
#print axioms choiceAlternatingSum_zero_of_local_constraints
#print axioms binaryChoiceFan_abstract_cancellation
end LC004

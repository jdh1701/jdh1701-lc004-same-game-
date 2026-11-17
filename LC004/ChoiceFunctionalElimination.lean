import LC004.ChoiceReducedCancellation

namespace LC004

/-- Several dominated vertices may have different dominators, provided every
dominator survives the entire deletion. -/
theorem facetAlternatingSum_delete_set_varying {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (U : Finset α)
    (hdom : ∀ u ∈ U, ∃ w, w ∉ U ∧ ∀ f ∈ facets, u ∈ f → w ∈ f) :
    faceAlternatingSum (facetFaces facets) =
      faceAlternatingSum (facetFaces (facets.image (fun f => f \ U))) := by
  classical
  induction U using Finset.induction_on generalizing facets with
  | empty => simp
  | @insert v U hv ih =>
    obtain ⟨w, hw, hfw⟩ := hdom v (Finset.mem_insert_self _ _)
    have hvw : v ≠ w := by intro h; subst v; exact hw (Finset.mem_insert_self _ _)
    rw [facetAlternatingSum_erase_dominated facets v w hvw hfw]
    have hd : ∀ u ∈ U, ∃ z, z ∉ U ∧
        ∀ f ∈ facets.image (fun f => f.erase v), u ∈ f → z ∈ f := by
      intro u hu
      obtain ⟨z, hz, hgz⟩ := hdom u (Finset.mem_insert_of_mem hu)
      refine ⟨z, fun h => hz (Finset.mem_insert_of_mem h), ?_⟩
      intro f hf huf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_erase.mpr
        ⟨fun h => hz (h ▸ Finset.mem_insert_self v U),
          hgz g hg (Finset.mem_of_mem_erase huf)⟩
    have h := ih (facets.image (fun f => f.erase v)) hd
    have heq : ∀ f : Finset α, f.erase v \ U = f \ insert v U := by
      intro f; ext x; simp; tauto
    simpa only [Finset.image_image, Function.comp_def, heq] using h

/-- Deleting an entire coordinate preserves the face sum whenever each of its
values forces a value in another retained coordinate. Bijections satisfy this
hypothesis, but injectivity of the determining function is unnecessary here.
The reduced facets remain in the original vertex universe, avoiding any hidden
assumption about relabeling or a new constraint system. -/
theorem choiceAlternatingSum_delete_determined_coordinate {ι : Type*} {D : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (i j : ι) (hij : i ≠ j)
    (hdet : ∀ x : D i, ∃ y : D j, ∀ a ∈ A, a i = x → a j = y) :
    faceAlternatingSum (facetFaces (choiceFacets A)) =
      faceAlternatingSum (facetFaces ((choiceFacets A).image
        (fun f => f \ Finset.univ.image (Sigma.mk i)))) := by
  classical
  apply facetAlternatingSum_delete_set_varying
  intro v hv
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨y, hy⟩ := hdet x
  refine ⟨Sigma.mk j y, ?_, ?_⟩
  · intro hm
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hm
    exact hij (congrArg Sigma.fst hz)
  · intro f hf hif
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
    exact (mem_choiceFacet a j y).mpr (hy a ha ((mem_choiceFacet a i x).mp hif))

theorem choiceAlternatingSum_delete_bijective_coordinate {ι : Type*} {D : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (i j : ι) (hij : i ≠ j)
    (hbij : ChoiceRelationBijective (ChoicePairProjection A i j)) :
    faceAlternatingSum (facetFaces (choiceFacets A)) =
      faceAlternatingSum (facetFaces ((choiceFacets A).image
        (fun f => f \ Finset.univ.image (Sigma.mk i)))) := by
  apply choiceAlternatingSum_delete_determined_coordinate A i j hij
  intro x
  obtain ⟨y, _, hy⟩ := hbij.1 x
  exact ⟨y, fun a ha hx => hy (a j) ⟨a, ha, hx, rfl⟩⟩

#print axioms facetAlternatingSum_delete_set_varying
#print axioms choiceAlternatingSum_delete_determined_coordinate
#print axioms choiceAlternatingSum_delete_bijective_coordinate
end LC004

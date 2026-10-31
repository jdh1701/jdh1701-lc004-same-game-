import LC004.ChoiceUniversalValue

namespace LC004

theorem facetAlternatingSum_delete_set {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (U : Finset α) (w : α) (hw : w ∉ U)
    (hdom : ∀ u ∈ U, ∀ f ∈ facets, u ∈ f → w ∈ f) :
    faceAlternatingSum (facetFaces facets) =
      faceAlternatingSum (facetFaces (facets.image (fun f => f \ U))) := by
  classical
  induction U using Finset.induction_on generalizing facets with
  | empty => simp
  | @insert v U hv ih =>
    have hvw : v ≠ w := by intro h; subst v; exact hw (Finset.mem_insert_self _ _)
    have hwU : w ∉ U := fun h => hw (Finset.mem_insert_of_mem h)
    rw [facetAlternatingSum_erase_dominated facets v w hvw
      (fun f hf hfv => hdom v (Finset.mem_insert_self _ _) f hf hfv)]
    have hd : ∀ u ∈ U, ∀ f ∈ facets.image (fun f => f.erase v), u ∈ f → w ∈ f := by
      intro u hu f hf huf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_erase.mpr ⟨hvw.symm,
        hdom u (Finset.mem_insert_of_mem hu) g hg (Finset.mem_of_mem_erase huf)⟩
    have h := ih (facets.image (fun f => f.erase v)) hwU hd
    have heq : ∀ f : Finset α, f.erase v \ U = f \ insert v U := by
      intro f; ext x; simp; tauto
    simpa only [Finset.image_image, Function.comp_def, heq] using h

/-- Delete a set of vertices dominated by a common surviving vertex. If the
remaining faces extend to a cone point, the original alternating sum vanishes. -/
theorem facetAlternatingSum_zero_of_deletion_cone {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (U : Finset α) (w x : α) (hw : w ∉ U)
    (hdom : ∀ u ∈ U, ∀ f ∈ facets, u ∈ f → w ∈ f)
    (hreplace : ∀ f ∈ facets,
      insert x (f \ U) ∈ facetFaces (facets.image (fun f => f \ U))) :
    faceAlternatingSum (facetFaces facets) = 0 := by
  classical
  rw [facetAlternatingSum_delete_set facets U w hw hdom]
  apply faceAlternatingSum_zero_of_cone _ x
  · intro s hs
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces _ _).mp hs
    exact (mem_facetFaces _ _).mpr ⟨f, hf, (Finset.erase_subset _ _).trans hsf⟩
  · intro s hs
    obtain ⟨f, hf, hsf⟩ := (mem_facetFaces _ _).mp hs
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨t, ht, hgt⟩ := (mem_facetFaces _ _).mp (hreplace g hg)
    exact (mem_facetFaces _ _).mpr ⟨t, ht, (Finset.insert_subset_insert x hsf).trans hgt⟩

noncomputable def choiceFacet {ι : Type*} {D : ι → Type*} [Fintype ι]
    (a : ∀ i, D i) : Finset (Sigma D) := by
  classical
  exact Finset.univ.image (fun i => Sigma.mk i (a i))

theorem mem_choiceFacet {ι : Type*} {D : ι → Type*} [Fintype ι]
    (a : ∀ i, D i) (i : ι) (x : D i) :
    Sigma.mk i x ∈ choiceFacet a ↔ a i = x := by
  classical
  simp [choiceFacet, Sigma.mk.inj_iff]

noncomputable def choiceFacets {ι : Type*} {D : ι → Type*} [Fintype ι]
    (A : Finset (∀ i, D i)) : Finset (Finset (Sigma D)) := by
  classical
  exact A.image choiceFacet

theorem mem_choiceFacets {ι : Type*} {D : ι → Type*} [Fintype ι]
    (A : Finset (∀ i, D i)) (f : Finset (Sigma D)) :
    f ∈ choiceFacets A ↔ ∃ a ∈ A, choiceFacet a = f := by
  classical
  exact Finset.mem_image

/-- A universal replacement value and a distinct forced neighbor cancel the
whole choice-complex sum. No assumption about the number of solutions is used. -/
theorem choiceAlternatingSum_zero_of_replace_and_force {ι : Type*} {D : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (D i)]
    [∀ i, DecidableEq (D i)]
    (A : Finset (∀ i, D i)) (i j : ι) (hij : i ≠ j) (x : D i) (y : D j)
    (hreplace : ∀ a ∈ A, Function.update a i x ∈ A)
    (hforce : ∀ a ∈ A, a i ≠ x → a j = y) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  classical
  let U : Finset (Sigma D) := (Finset.univ.erase x).image (Sigma.mk i)
  have hxp : Sigma.mk i x ∉ U := by simp [U, Sigma.mk.inj_iff]
  have hwp : Sigma.mk j y ∉ U := by
    intro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    exact hij (congrArg Sigma.fst hu)
  apply facetAlternatingSum_zero_of_deletion_cone (choiceFacets A) U
    (Sigma.mk j y) (Sigma.mk i x) hwp
  · intro v hv f hf hvf
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
    have hai := (mem_choiceFacet a i u).mp hvf
    apply (mem_choiceFacet a j y).mpr
    apply hforce a ha
    intro hax
    exact (Finset.mem_erase.mp hu).1 (hai.symm.trans hax)
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
    apply (mem_facetFaces _ _).mpr
    refine ⟨choiceFacet (Function.update a i x) \ U, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨choiceFacet (Function.update a i x),
        (mem_choiceFacets A _).mpr ⟨_, hreplace a ha, rfl⟩, rfl⟩
    · apply Finset.insert_subset
      · exact Finset.mem_sdiff.mpr
          ⟨(mem_choiceFacet _ i x).mpr (Function.update_same _ _ _), hxp⟩
      · intro v hv
        obtain ⟨hv, hvU⟩ := Finset.mem_sdiff.mp hv
        rcases v with ⟨k, z⟩
        apply Finset.mem_sdiff.mpr
        refine ⟨(mem_choiceFacet _ k z).mpr ?_, hvU⟩
        by_cases hk : k = i
        · subst k
          have hzx : z = x := by
            by_cases hz : z = x
            · exact hz
            · exact (hvU (Finset.mem_image.mpr
                ⟨z, Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩, rfl⟩)).elim
          simpa [hzx] using Function.update_same a i x
        · simpa [Function.update_of_ne hk] using (mem_choiceFacet a k z).mp hv

/-- The cancellation theorem for the reduced constraint system: supported
domains, majority closure, binary determination, no bijective coordinate pair,
and a nonuniversal neighbor for each coordinate. Functional elimination and
the original-game identification are separate obligations. -/
theorem choiceAlternatingSum_zero_of_reduced_system {ι : Type*} {D : ι → Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [∀ i, Fintype (D i)]
    [∀ i, DecidableEq (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hclosed : ChoiceSolutionsClosed A)
    (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hbinary : ChoiceBinaryDetermined A)
    (hnobij : ∀ i j, i ≠ j → ¬ ChoiceRelationBijective (ChoicePairProjection A i j))
    (hneighbors : ∀ i, ∃ j, i ≠ j ∧ ¬ ∀ x y, ChoicePairProjection A i j x y) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  obtain ⟨i, x, hx⟩ := choice_exists_universal_value A hclosed hsupport hnobij
  obtain ⟨j, hij, hn⟩ := hneighbors i
  have hrows : ∀ u, ∃ v, ChoicePairProjection A i j u v := by
    intro u
    obtain ⟨a, ha, hai⟩ := hsupport i u
    exact ⟨a j, a, ha, hai, rfl⟩
  have hcols : ∀ v, ∃ u, ChoicePairProjection A i j u v := by
    intro v
    obtain ⟨a, ha, haj⟩ := hsupport j v
    exact ⟨a i, a, ha, rfl, haj⟩
  rcases choiceRelation_classification (choicePairProjection_closed hclosed i j)
      hrows hcols with hu | hb | hf
  · exact (hn hu).elim
  · exact (hnobij i j hij hb).elim
  · obtain ⟨p, q, hf⟩ := hf
    obtain ⟨z, hz⟩ := exists_ne q
    have hxp : x = p := ((hf x z).mp (hx j hij z)).resolve_right hz
    apply choiceAlternatingSum_zero_of_replace_and_force A i j hij x q
    · intro a ha
      exact choice_universal_value_replace A hbinary i x hx a ha
    · intro a ha hax
      have h := (hf (a i) (a j)).mp ⟨a, ha, rfl, rfl⟩
      exact h.resolve_left (fun hp => hax (hp.trans hxp.symm))

/-- A three-solution two-fan, used to check that the reduced theorem's
hypotheses can hold simultaneously. These checks use the Lean kernel. -/
def binaryChoiceFan : Finset (Fin 2 → Fin 2) :=
  Finset.univ.filter (fun a => a 0 = 0 ∨ a 1 = 0)

theorem binaryChoiceFan_card : binaryChoiceFan.card = 3 := by decide

theorem binaryChoiceFan_alternatingSum_zero :
    faceAlternatingSum (facetFaces (choiceFacets binaryChoiceFan)) = 0 := by
  apply choiceAlternatingSum_zero_of_reduced_system
  · unfold ChoiceSolutionsClosed
    decide
  · decide
  · unfold ChoiceBinaryDetermined ChoicePairProjection
    decide
  · unfold ChoiceRelationBijective ChoicePairProjection
    unfold ExistsUnique
    decide
  · unfold ChoicePairProjection
    decide

#print axioms facetAlternatingSum_delete_set
#print axioms choiceAlternatingSum_zero_of_replace_and_force
#print axioms choiceAlternatingSum_zero_of_reduced_system
#print axioms binaryChoiceFan_alternatingSum_zero
end LC004

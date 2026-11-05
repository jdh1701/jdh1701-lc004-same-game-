import LC004.ChoiceBijectiveQuotient

namespace LC004
open scoped Classical BigOperators

theorem facetFaces_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (f : α → β) :
    facetFaces (F.image (fun s => s.image f)) =
      (facetFaces F).image (fun s => s.image f) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨g, hg, hsg⟩ := (mem_facetFaces _ _).mp hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    let u := t.filter (fun x => f x ∈ s)
    apply Finset.mem_image.mpr
    refine ⟨u, (mem_facetFaces _ _).mpr ⟨t, ht, Finset.filter_subset _ _⟩, ?_⟩
    ext y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (hsg hy)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy.symm ▸ hy⟩, hxy⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨g, hg, htg⟩ := (mem_facetFaces _ _).mp ht
    exact (mem_facetFaces _ _).mpr
      ⟨g.image f, Finset.mem_image.mpr ⟨g, hg, rfl⟩, Finset.image_subset_image htg⟩

theorem facetAlternatingSum_image_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (f : α → β) (hf : Function.Injective f) :
    faceAlternatingSum (facetFaces (F.image (fun s => s.image f))) =
      faceAlternatingSum (facetFaces F) := by
  rw [facetFaces_image]
  unfold faceAlternatingSum
  rw [Finset.sum_image (fun _ _ _ _ h => Finset.image_injective hf h)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.card_image_of_injective s hf]

noncomputable def choiceRepresentativeEmbedding {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    (Sigma fun q : ChoiceCoordinateQuotient A hsupport => D q.out) ↪ Sigma D :=
  Function.Embedding.sigmaMap ⟨Quotient.out, Quotient.out_injective⟩
    (fun _ => Function.Embedding.refl _)

noncomputable def choiceDeletedVertices {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) : Finset (Sigma D) :=
  Finset.univ.filter (fun v => v.1 ≠ (Quotient.mk (choiceBijectiveSetoid A hsupport) v.1).out)

theorem mem_choiceDeletedVertices {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) (v : Sigma D) :
    v ∈ choiceDeletedVertices A hsupport ↔
      v.1 ≠ (Quotient.mk (choiceBijectiveSetoid A hsupport) v.1).out := by
  simp [choiceDeletedVertices]

theorem choiceFacet_delete_representatives {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) (a : ∀ i, D i) :
    choiceFacet a \ choiceDeletedVertices A hsupport =
      (choiceFacet (fun q : ChoiceCoordinateQuotient A hsupport => a q.out)).image
        (choiceRepresentativeEmbedding A hsupport) := by
  classical
  ext v
  rcases v with ⟨i, x⟩
  constructor
  · intro h
    obtain ⟨hface, hnot⟩ := Finset.mem_sdiff.mp h
    have hai := (mem_choiceFacet a i x).mp hface
    have hi : i = (Quotient.mk (choiceBijectiveSetoid A hsupport) i).out := by
      by_contra hn
      exact hnot ((mem_choiceDeletedVertices A hsupport _).mpr hn)
    let q := Quotient.mk (choiceBijectiveSetoid A hsupport) i
    refine Finset.mem_image.mpr ⟨Sigma.mk q (a q.out), ?_, ?_⟩
    · exact (mem_choiceFacet _ q _).mpr rfl
    · change (Sigma.mk q.out (a q.out) : Sigma D) = Sigma.mk i x
      exact (congrArg (fun k => Sigma.mk k (a k)) hi.symm).trans (congrArg (Sigma.mk i) hai)
  · intro h
    obtain ⟨⟨q, z⟩, hqz, heq⟩ := Finset.mem_image.mp h
    have hz : a q.out = z :=
      (mem_choiceFacet (fun q : ChoiceCoordinateQuotient A hsupport => a q.out) q z).mp hqz
    rw [← heq]
    change Sigma.mk q.out z ∈ choiceFacet a \ choiceDeletedVertices A hsupport
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_choiceFacet a q.out z).mpr hz, ?_⟩
    intro hm
    have hn := (mem_choiceDeletedVertices A hsupport _).mp hm
    exact hn (congrArg Quotient.out (Quotient.out_eq q)).symm

theorem choiceQuotient_restrict_mem {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (a : ∀ i, D i) (ha : a ∈ A) :
    (fun q : ChoiceCoordinateQuotient A hsupport => a q.out) ∈ choiceQuotientFamily A hsupport := by
  apply (mem_choiceReducedFamily A _ _ _).mpr
  have h : choiceCoordinateLift (Quotient.mk _) (choiceQuotientEquiv A hsupport)
      (fun q : ChoiceCoordinateQuotient A hsupport => a q.out) = a := by
    funext i
    exact choiceQuotientEquiv_on_solution A hsupport a ha i
  exact h.symm ▸ ha

theorem choiceQuotient_restrict_surjective {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (b : ∀ q : ChoiceCoordinateQuotient A hsupport, D q.out)
    (hb : b ∈ choiceQuotientFamily A hsupport) :
    ∃ a ∈ A, (fun q : ChoiceCoordinateQuotient A hsupport => a q.out) = b := by
  let a := choiceCoordinateLift (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out)
    (Quotient.mk _) (choiceQuotientEquiv A hsupport) b
  have ha : a ∈ A := (mem_choiceReducedFamily A _ _ b).mp hb
  refine ⟨a, ha, ?_⟩
  apply choiceCoordinateLift_injective (E := fun q : ChoiceCoordinateQuotient A hsupport => D q.out)
    (Quotient.mk _) (choiceQuotientEquiv A hsupport) Quotient.mk_surjective
  funext i
  exact choiceQuotientEquiv_on_solution A hsupport a ha i

theorem choiceQuotient_facets_image {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    (choiceFacets A).image (fun f => f \ choiceDeletedVertices A hsupport) =
      (choiceFacets (choiceQuotientFamily A hsupport)).image
        (fun f => f.image (choiceRepresentativeEmbedding A hsupport)) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A g).mp hg
    exact Finset.mem_image.mpr ⟨_,
      (mem_choiceFacets _ _).mpr ⟨_, choiceQuotient_restrict_mem A hsupport a ha, rfl⟩,
      (choiceFacet_delete_representatives A hsupport a).symm⟩
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨b, hb, rfl⟩ := (mem_choiceFacets _ g).mp hg
    obtain ⟨a, ha, hab⟩ := choiceQuotient_restrict_surjective A hsupport b hb
    refine Finset.mem_image.mpr ⟨_, (mem_choiceFacets A _).mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [choiceFacet_delete_representatives A hsupport a, hab]

theorem choiceAlternatingSum_quotient {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x) :
    faceAlternatingSum (facetFaces (choiceFacets A)) =
      faceAlternatingSum (facetFaces (choiceFacets (choiceQuotientFamily A hsupport))) := by
  classical
  rw [facetAlternatingSum_delete_set_varying (choiceFacets A) (choiceDeletedVertices A hsupport) ?_]
  · rw [choiceQuotient_facets_image]
    exact facetAlternatingSum_image_embedding _ _ (choiceRepresentativeEmbedding A hsupport).injective
  · intro v hv
    rcases v with ⟨i, x⟩
    let q := Quotient.mk (choiceBijectiveSetoid A hsupport) i
    let e := choiceQuotientEquiv A hsupport i
    refine ⟨Sigma.mk q.out (e.symm x), ?_, ?_⟩
    · intro hm
      exact ((mem_choiceDeletedVertices A hsupport _).mp hm)
        (congrArg Quotient.out (Quotient.out_eq q)).symm
    · intro f hf hvf
      obtain ⟨a, ha, rfl⟩ := (mem_choiceFacets A f).mp hf
      apply (mem_choiceFacet a q.out _).mpr
      apply e.injective
      rw [e.apply_symm_apply]
      exact (choiceQuotientEquiv_on_solution A hsupport a ha i).trans
        ((mem_choiceFacet a i x).mp hvf)

theorem choiceAlternatingSum_zero_of_nontrivial_quotient {ι : Type*} {D : ι → Type*}
    [Fintype ι] [∀ i, Fintype (D i)] [∀ i, Nontrivial (D i)]
    (A : Finset (∀ i, D i)) (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    [Nontrivial (ChoiceCoordinateQuotient A hsupport)]
    (hclosed : ChoiceSolutionsClosed A) (hbinary : ChoiceBinaryDetermined A)
    (hconn : ChoiceCoordinatesConnected A) :
    faceAlternatingSum (facetFaces (choiceFacets A)) = 0 := by
  rw [choiceAlternatingSum_quotient A hsupport]
  exact choiceQuotientFamily_alternatingSum_zero A hsupport hclosed hbinary hconn

#print axioms choiceAlternatingSum_quotient
#print axioms choiceAlternatingSum_zero_of_nontrivial_quotient
end LC004

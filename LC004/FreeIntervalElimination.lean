import LC004.ExclusiveSeparatorElimination
import LC004.ClassCutSeparators

namespace LC004
open scoped Classical

/-- All cofaces of sigma in a unique facet tau have zero alternating sum when
tau has a vertex outside sigma. This cancels a whole Boolean interval at once. -/
theorem faceAlternatingSum_free_interval_zero {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (sigma tau : Finset α) (w : α)
    (htau : tau ∈ facets) (hw : w ∈ tau) (hws : w ∉ sigma)
    (hunique : ∀ f ∈ facets, sigma ⊆ f → f = tau) :
    faceAlternatingSum ((facetFaces facets).filter (sigma ⊆ ·)) = 0 := by
  classical
  apply faceAlternatingSum_zero_of_cone _ w
  · intro s hs
    obtain ⟨hsF,hss⟩ := Finset.mem_filter.mp hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hsF
    apply Finset.mem_filter.mpr
    refine ⟨(mem_facetFaces _ _).mpr ⟨f,hf,(Finset.erase_subset _ _).trans hsf⟩,?_⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun he => hws (he ▸ hx),hss hx⟩
  · intro s hs
    obtain ⟨hsF,hss⟩ := Finset.mem_filter.mp hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hsF
    have he := hunique f hf (hss.trans hsf)
    subst f
    exact Finset.mem_filter.mpr
      ⟨(mem_facetFaces _ _).mpr ⟨tau,htau,Finset.insert_subset hw hsf⟩,
        hss.trans (Finset.subset_insert _ _)⟩

/-- Removing a free interval preserves the signed face sum, even when its
codimension is larger than one. The lower face need not be a large face. -/
theorem faceAlternatingSum_remove_free_interval {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (sigma tau : Finset α) (w : α)
    (htau : tau ∈ facets) (hw : w ∈ tau) (hws : w ∉ sigma)
    (hunique : ∀ f ∈ facets, sigma ⊆ f → f = tau) :
    faceAlternatingSum (facetFaces facets) =
      faceAlternatingSum ((facetFaces facets).filter (fun s => ¬ sigma ⊆ s)) := by
  classical
  have hz := faceAlternatingSum_free_interval_zero facets sigma tau w htau hw hws hunique
  have h := Finset.sum_filter_add_sum_filter_not (facetFaces facets)
    (sigma ⊆ ·) (fun s => (-1 : Int)^s.card)
  change faceAlternatingSum ((facetFaces facets).filter (sigma ⊆ ·)) +
    faceAlternatingSum ((facetFaces facets).filter (fun s => ¬ sigma ⊆ s)) =
      faceAlternatingSum (facetFaces facets) at h
  rw [hz,zero_add] at h
  exact h.symm

/-- Sparse implementation of free-interval removal: replace the unique facet
by its erasures at the lower-face vertices. No full face enumeration is needed. -/
theorem facetFaces_remove_free_interval {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (sigma tau : Finset α)
    (htau : tau ∈ facets)
    (hunique : ∀ f ∈ facets, sigma ⊆ f → f = tau) :
    facetFaces (facets.erase tau ∪ sigma.image (fun v => tau.erase v)) =
      (facetFaces facets).filter (fun s => ¬ sigma ⊆ s) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
    apply Finset.mem_filter.mpr
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨hne,hf⟩ := Finset.mem_erase.mp hf
      exact ⟨(mem_facetFaces _ _).mpr ⟨f,hf,hsf⟩,
        fun h => hne (hunique f hf (h.trans hsf))⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(mem_facetFaces _ _).mpr
        ⟨tau,htau,hsf.trans (Finset.erase_subset _ _)⟩,
        fun h => (Finset.mem_erase.mp (hsf (h hv))).1 rfl⟩
  · intro hs
    obtain ⟨hsF,hnot⟩ := Finset.mem_filter.mp hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hsF
    apply (mem_facetFaces _ _).mpr
    by_cases he : f = tau
    · subst f
      obtain ⟨v,hv,hvs⟩ := Finset.not_subset.mp hnot
      refine ⟨tau.erase v,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩),?_⟩
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hvs (h ▸ hx),hsf hx⟩
    · exact ⟨f,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hf⟩),hsf⟩

/-- Sparse free-interval removal is valid for the ORIGINAL coefficient on the
canonical classwise separator complex. -/
theorem winningJoinCoefficient_remove_free_interval {n : Nat}
    (p : ColorPattern n) (sigma tau : Finset (ColorPattern n)) (w : ColorPattern n)
    (htau : tau ∈ certificateCoarseningFacets p (classCutSeparators p))
    (hw : w ∈ tau) (hws : w ∉ sigma)
    (hunique : ∀ f ∈ certificateCoarseningFacets p (classCutSeparators p),
      sigma ⊆ f → f = tau) :
    winningJoinCoefficient n p = faceAlternatingSum
      (facetFaces ((certificateCoarseningFacets p (classCutSeparators p)).erase tau ∪
        sigma.image (fun v => tau.erase v))) := by
  rw [winningJoinCoefficient_eq_class_cut_face_sum,
    facetFaces_remove_free_interval _ sigma tau htau hunique]
  exact faceAlternatingSum_remove_free_interval _ sigma tau w htau hw hws hunique

#print axioms faceAlternatingSum_free_interval_zero
#print axioms faceAlternatingSum_remove_free_interval
#print axioms winningJoinCoefficient_remove_free_interval
end LC004

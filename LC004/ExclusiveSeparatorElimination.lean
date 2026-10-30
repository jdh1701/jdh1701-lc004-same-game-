import LC004.SeparatorDeletionLink

namespace LC004
open scoped BigOperators

/-- Remove all marked vertices at once, retaining exactly the avoiding faces. -/
def avoidMarkedFaces {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (V : Finset α) : Finset (Finset α) :=
  F.filter (fun s => Disjoint s V)

/-- Simultaneous deletion is implemented directly on facets. -/
theorem avoidMarkedFaces_facetFaces {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (V : Finset α) :
    avoidMarkedFaces (facetFaces facets) V =
      facetFaces (facets.image (fun f => f \ V)) := by
  ext s
  simp only [avoidMarkedFaces,Finset.mem_filter,mem_facetFaces,Finset.mem_image]
  constructor
  · rintro ⟨⟨f,hf,hsf⟩,hd⟩
    refine ⟨f \ V,⟨f,hf,rfl⟩,?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hsf hx,fun hV => Finset.disjoint_left.mp hd hx hV⟩
  · rintro ⟨_,⟨f,hf,rfl⟩,hs⟩
    refine ⟨⟨f,hf,fun x hx => (Finset.mem_sdiff.mp (hs hx)).1⟩,?_⟩
    exact Finset.disjoint_left.mpr (fun x hx hV => (Finset.mem_sdiff.mp (hs hx)).2 hV)

/-- If no face can contain two marked vertices, their links have disjoint
contributions. This eliminates the marked variable in one exact step. -/
theorem faceAlternatingSum_eliminate_exclusive {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (V : Finset α)
    (hexclusive : ∀ s ∈ F, ∀ v ∈ V, ∀ w ∈ V, v ∈ s → w ∈ s → v = w) :
    faceAlternatingSum F = faceAlternatingSum (avoidMarkedFaces F V) -
      ∑ v ∈ V, faceAlternatingSum (separatorLink F v) := by
  classical
  let C := fun v => F.filter (v ∈ ·)
  have hdisj : (V : Set α).PairwiseDisjoint C := by
    intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro s hs ht
    exact hne (hexclusive s (Finset.mem_filter.mp hs).1 v hv w hw
      (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2)
  have hpart : F = avoidMarkedFaces F V ∪ V.biUnion C := by
    ext s
    simp only [avoidMarkedFaces,Finset.mem_union,Finset.mem_filter,
      Finset.mem_biUnion,C]
    constructor
    · intro hs
      by_cases hd : Disjoint s V
      · exact Or.inl ⟨hs,hd⟩
      · apply Or.inr
        obtain ⟨v,hvs,hvV⟩ := Finset.not_disjoint_iff.mp hd
        exact ⟨v,hvV,hs,hvs⟩
    · rintro (⟨hs,_⟩ | ⟨v,_,hs,_⟩) <;> exact hs
  have hd : Disjoint (avoidMarkedFaces F V) (V.biUnion C) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨v,hv,hsv⟩ := Finset.mem_biUnion.mp ht
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp hs).2
      (Finset.mem_filter.mp hsv).2 hv
  have hC (v : α) : faceAlternatingSum (C v) =
      -faceAlternatingSum (separatorLink F v) := by
    have h := faceAlternatingSum_deletion_link F v
    have hs := Finset.sum_filter_add_sum_filter_not F (fun s => v ∈ s)
      (fun s => (-1 : Int)^s.card)
    unfold faceAlternatingSum separatorDeletion at h
    unfold faceAlternatingSum
    dsimp [C]
    linarith
  calc
    faceAlternatingSum F = faceAlternatingSum (avoidMarkedFaces F V) +
        ∑ v ∈ V, faceAlternatingSum (C v) := by
      conv_lhs => rw [hpart]
      unfold faceAlternatingSum
      rw [Finset.sum_union hd,Finset.sum_biUnion hdisj]
    _ = _ := by simp_rw [hC]; rw [Finset.sum_neg_distrib]; ring

/-- A common vertex in every facet is an explicit vanishing certificate.
Empty facet families are allowed and have alternating sum zero. -/
theorem facetAlternatingSum_zero_of_common_vertex {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (w : α)
    (hcommon : ∀ f ∈ facets, w ∈ f) :
    faceAlternatingSum (facetFaces facets) = 0 := by
  apply faceAlternatingSum_zero_of_cone _ w
  · intro s hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
    exact (mem_facetFaces _ _).mpr ⟨f,hf,(Finset.erase_subset _ _).trans hsf⟩
  · intro s hs
    obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
    exact (mem_facetFaces _ _).mpr ⟨f,hf,Finset.insert_subset (hcommon f hf) hsf⟩

/-- If every facet using v also uses a distinct partner w, the link at v is a
cone. This is a combinatorial criterion, not an assumed numerical cancellation. -/
theorem separatorLink_zero_of_common_partner {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (v w : α) (hvw : v ≠ w)
    (hpartner : ∀ f ∈ facets, v ∈ f → w ∈ f) :
    faceAlternatingSum (separatorLink (facetFaces facets) v) = 0 := by
  rw [separatorLink_facetFaces]
  apply facetAlternatingSum_zero_of_common_vertex _ w
  intro f hf
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨hg,hvg⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_erase.mpr ⟨Ne.symm hvw,hpartner g hg hvg⟩

/-- A dominant row cancels the projection; all other rows vanish by their
explicit common-partner certificates. -/
theorem faceAlternatingSum_zero_of_dominant_row {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (V : Finset α) (v : α) (hv : v ∈ V)
    (hexclusive : ∀ s ∈ facetFaces facets, ∀ a ∈ V, ∀ b ∈ V,
      a ∈ s → b ∈ s → a = b)
    (hrow : avoidMarkedFaces (facetFaces facets) V = separatorLink (facetFaces facets) v)
    (hothers : ∀ w ∈ V, w ≠ v → ∃ z, w ≠ z ∧
      ∀ f ∈ facets, w ∈ f → z ∈ f) : faceAlternatingSum (facetFaces facets) = 0 := by
  rw [faceAlternatingSum_eliminate_exclusive _ V hexclusive,hrow]
  have hs : (∑ w ∈ V, faceAlternatingSum (separatorLink (facetFaces facets) w)) =
      faceAlternatingSum (separatorLink (facetFaces facets) v) := by
    apply Finset.sum_eq_single v
    · intro w hw hne
      obtain ⟨z,hwz,hz⟩ := hothers w hw hne
      exact separatorLink_zero_of_common_partner facets w z hwz hz
    · exact fun h => (h hv).elim
  rw [hs,sub_self]

/-- Application to ORIGINAL coefficients. The only extra condition is the
explicit exclusivity of marked separators within each certificate facet. -/
theorem winningJoinCoefficient_eliminate_exclusive {n : Nat} {β : Type*}
    [DecidableEq β] (p : ColorPattern n) (V M : Finset β) (sep : β → ColorPattern n)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v)
    (hexclusive : ∀ c, CertificateConstraint c → c ≤ p →
      ∀ v ∈ M, ∀ w ∈ M, c ≤ sep v → c ≤ sep w → v = w) :
    let F := facetFaces (indexedCertificateCoarseningFacets p V sep)
    winningJoinCoefficient n p = faceAlternatingSum (avoidMarkedFaces F M) -
      ∑ v ∈ M, faceAlternatingSum (separatorLink F v) := by
  classical
  dsimp only
  rw [winningJoinCoefficient_eq_indexed_face_sum p V sep hproper hcover]
  apply faceAlternatingSum_eliminate_exclusive
  intro s hs v hv w hw hvs hws
  obtain ⟨f,hf,hsf⟩ := (mem_facetFaces _ _).mp hs
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hf
  have hc' := Finset.mem_filter.mp hc
  exact hexclusive c hc'.2.1 hc'.2.2 v hv w hw
    (Finset.mem_filter.mp (hsf hvs)).2 (Finset.mem_filter.mp (hsf hws)).2

#print axioms faceAlternatingSum_eliminate_exclusive
#print axioms winningJoinCoefficient_eliminate_exclusive
end LC004

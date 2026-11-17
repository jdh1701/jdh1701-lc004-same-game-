import LC004.IncidenceFaceSum

namespace LC004
open scoped BigOperators

/-- The faces avoiding a specified separator. -/
def separatorDeletion {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (v : α) : Finset (Finset α) := F.filter (v ∉ ·)

/-- Remove a specified separator from all faces containing it. -/
def separatorLink {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  (F.filter (v ∈ ·)).image (fun s => s.erase v)

/-- Exact signed deletion/link recurrence. No topological regularity, nonempty
complex, or contractibility hypothesis is required. -/
theorem faceAlternatingSum_deletion_link {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (v : α) :
    faceAlternatingSum F =
      faceAlternatingSum (separatorDeletion F v) -
        faceAlternatingSum (separatorLink F v) := by
  classical
  have hinj : ∀ s ∈ F.filter (v ∈ ·), ∀ t ∈ F.filter (v ∈ ·),
      s.erase v = t.erase v → s = t := by
    intro s hs t ht he
    have hvs := (Finset.mem_filter.mp hs).2
    have hvt := (Finset.mem_filter.mp ht).2
    calc
      s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
      _ = insert v (t.erase v) := congrArg (insert v) he
      _ = t := Finset.insert_erase hvt
  have hs : faceAlternatingSum (separatorLink F v) =
      -(∑ s ∈ F.filter (v ∈ ·), (-1 : Int)^s.card) := by
    unfold faceAlternatingSum separatorLink
    rw [Finset.sum_image hinj,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hv := (Finset.mem_filter.mp hs).2
    have hc := Finset.card_erase_add_one hv
    rw [← hc,pow_succ]
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun s => v ∈ s)
    (fun s => (-1 : Int)^s.card)
  unfold faceAlternatingSum separatorDeletion at *
  rw [hs]
  linarith

/-- A single free face/coface pair cancels. The incidence condition used by an
actual elementary simplicial collapse is stronger than needed for the sum. -/
theorem faceAlternatingSum_erase_pair {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (s t : Finset α) (hs : s ∈ F) (ht : t ∈ F)
    (hcard : t.card = s.card + 1) :
    faceAlternatingSum F = faceAlternatingSum ((F.erase s).erase t) := by
  have hne : t ≠ s := by intro he; rw [he] at hcard; omega
  have ht' : t ∈ F.erase s := Finset.mem_erase.mpr ⟨hne,ht⟩
  have ha := Finset.sum_erase_add F (fun u => (-1 : Int)^u.card) hs
  have hb := Finset.sum_erase_add (F.erase s) (fun u => (-1 : Int)^u.card) ht'
  have hz : (-1 : Int)^s.card + (-1 : Int)^t.card = 0 := by
    rw [hcard,pow_succ]; ring
  unfold faceAlternatingSum
  linarith

/-- Deletion and link can both be represented by facets, without enumerating
all faces. This is the representation used by the exact decision algorithm. -/
theorem separatorDeletion_facetFaces {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (v : α) :
    separatorDeletion (facetFaces facets) v =
      facetFaces (facets.image (fun f => f.erase v)) := by
  ext s
  simp only [separatorDeletion,Finset.mem_filter,mem_facetFaces,Finset.mem_image]
  constructor
  · rintro ⟨⟨f,hf,hsf⟩,hv⟩
    exact ⟨f.erase v,⟨f,hf,rfl⟩,fun x hx =>
      Finset.mem_erase.mpr ⟨fun he => hv (he ▸ hx),hsf hx⟩⟩
  · rintro ⟨_,⟨f,hf,rfl⟩,hs⟩
    exact ⟨⟨f,hf,hs.trans (Finset.erase_subset _ _)⟩,
      fun hv => Finset.not_mem_erase v f (hs hv)⟩

theorem separatorLink_facetFaces {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (v : α) :
    separatorLink (facetFaces facets) v =
      facetFaces ((facets.filter (v ∈ ·)).image (fun f => f.erase v)) := by
  classical
  ext s
  simp only [separatorLink,Finset.mem_image,Finset.mem_filter,mem_facetFaces]
  constructor
  · rintro ⟨t,⟨⟨f,hf,htf⟩,hvt⟩,rfl⟩
    exact ⟨f.erase v,⟨f,⟨hf,htf hvt⟩,rfl⟩,Finset.erase_subset_erase v htf⟩
  · rintro ⟨_,⟨f,⟨hf,hvf⟩,rfl⟩,hs⟩
    have hvs : v ∉ s := fun hv => Finset.not_mem_erase v f (hs hv)
    refine ⟨insert v s,⟨⟨f,hf,Finset.insert_subset hvf
      (hs.trans (Finset.erase_subset _ _))⟩,Finset.mem_insert_self _ _⟩,?_⟩
    simp [hvs]

theorem facetAlternatingSum_deletion_link {α : Type*} [DecidableEq α]
    (facets : Finset (Finset α)) (v : α) :
    faceAlternatingSum (facetFaces facets) =
      faceAlternatingSum (facetFaces (facets.image (fun f => f.erase v))) -
      faceAlternatingSum (facetFaces
        ((facets.filter (v ∈ ·)).image (fun f => f.erase v))) := by
  rw [faceAlternatingSum_deletion_link _ v,separatorDeletion_facetFaces,
    separatorLink_facetFaces]

/-- Facet normalization is exact whenever each discarded facet is contained in
a retained facet. Duplicate and nonmaximal facets contribute no multiplicity. -/
theorem facetFaces_eq_of_mutual_cover {α : Type*} [DecidableEq α]
    (A B : Finset (Finset α))
    (hAB : ∀ a ∈ A, ∃ b ∈ B, a ⊆ b)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, b ⊆ a) : facetFaces A = facetFaces B := by
  ext s
  simp only [mem_facetFaces]
  constructor
  · rintro ⟨a,ha,hsa⟩
    obtain ⟨b,hb,hab⟩ := hAB a ha
    exact ⟨b,hb,hsa.trans hab⟩
  · rintro ⟨b,hb,hsb⟩
    obtain ⟨a,ha,hba⟩ := hBA b hb
    exact ⟨a,ha,hsb.trans hba⟩

/-- A checkable elementary collapse trace. The unique-coface condition records
the actual topological operation, beyond the weaker Euler cancellation. -/
inductive ElementaryFaceTrace {α : Type*} [DecidableEq α] :
    Finset (Finset α) → Finset (Finset α) → Prop where
  | refl (F) : ElementaryFaceTrace F F
  | next {F G : Finset (Finset α)} (s t : Finset α)
      (hs : s ∈ F) (ht : t ∈ F) (hsub : s ⊆ t)
      (hcard : t.card = s.card + 1)
      (hfree : ∀ u ∈ F, s ⊆ u → u = s ∨ u = t)
      (rest : ElementaryFaceTrace ((F.erase s).erase t) G) : ElementaryFaceTrace F G

theorem faceAlternatingSum_elementary_trace {α : Type*} [DecidableEq α]
    {F G : Finset (Finset α)} (h : ElementaryFaceTrace F G) :
    faceAlternatingSum F = faceAlternatingSum G := by
  induction h with
  | refl => rfl
  | next s t hs ht hsub hcard hfree rest ih =>
    exact (faceAlternatingSum_erase_pair _ s t hs ht hcard).trans ih

/-- The deletion/link recurrence computes the ORIGINAL coefficient when applied
to any complete separating family, for arbitrary class-size profiles. -/
theorem winningJoinCoefficient_separator_deletion_link {n : Nat} {β : Type*}
    [DecidableEq β] (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v) (v : β) :
    winningJoinCoefficient n p =
      faceAlternatingSum (separatorDeletion
        (facetFaces (indexedCertificateCoarseningFacets p V sep)) v) -
      faceAlternatingSum (separatorLink
        (facetFaces (indexedCertificateCoarseningFacets p V sep)) v) := by
  rw [winningJoinCoefficient_eq_indexed_face_sum p V sep hproper hcover]
  exact faceAlternatingSum_deletion_link _ v

/-- Any verified elementary-collapse trace from the actual separator complex
to a point proves vanishing of the original coefficient. -/
theorem winningJoinCoefficient_zero_of_elementary_trace {n : Nat} {β : Type*}
    [DecidableEq β] (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v) (v : β)
    (htrace : ElementaryFaceTrace
      (facetFaces (indexedCertificateCoarseningFacets p V sep)) ({v} : Finset β).powerset) :
    winningJoinCoefficient n p = 0 := by
  rw [winningJoinCoefficient_eq_indexed_face_sum p V sep hproper hcover,
    faceAlternatingSum_elementary_trace htrace]
  unfold faceAlternatingSum
  rw [Finset.sum_powerset_neg_one_pow_card]
  simp

#print axioms winningJoinCoefficient_zero_of_elementary_trace
#print axioms facetAlternatingSum_deletion_link
#print axioms faceAlternatingSum_deletion_link
#print axioms faceAlternatingSum_erase_pair
#print axioms winningJoinCoefficient_separator_deletion_link
end LC004

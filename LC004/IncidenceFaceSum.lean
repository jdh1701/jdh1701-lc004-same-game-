import LC004.CollectedJoinCoefficients
import LC004.ChoiceComplexCancellation

namespace LC004
open scoped BigOperators Classical

/-- Any cofinal collection of proper refinements below p isolates one incidence
coefficient through alternating subsets. Coatoms are optional, not assumed. -/
theorem separating_map_powerset_incidence {α β : Type*} [Fintype α]
    [SemilatticeInf α] [OrderTop α] (f : α → Int) (p : α) (V : Finset β) (sep : β → α)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v) :
    (∑ S ∈ V.powerset, (-1 : Int)^S.card * lowerIncidence f (p ⊓ S.inf sep)) = f p := by
  classical
  unfold lowerIncidence
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (q : α) :
      (∑ S ∈ V.powerset, (-1 : Int)^S.card *
        (if q ≤ p ⊓ S.inf sep then f q else 0)) = if q = p then f q else 0 := by
    have ht : V.powerset.filter (fun S => q ≤ p ⊓ S.inf sep) =
        if q ≤ p then (V.filter (fun v => q ≤ sep v)).powerset else ∅ := by
      ext S
      by_cases hqp : q ≤ p
      · simp only [Finset.mem_filter,Finset.mem_powerset,le_inf_iff,Finset.le_inf_iff,
          hqp,true_and,if_pos]
        constructor
        · rintro ⟨hSV,hqS⟩ v hv
          exact Finset.mem_filter.mpr ⟨hSV hv,hqS v hv⟩
        · intro hS
          exact ⟨fun v hv => (Finset.mem_filter.mp (hS hv)).1,
            fun v hv => (Finset.mem_filter.mp (hS hv)).2⟩
      · simp [hqp,le_inf_iff]
    simp_rw [mul_ite,mul_zero]
    rw [← Finset.sum_filter,ht]
    by_cases hqp : q ≤ p
    · rw [if_pos hqp,← Finset.sum_mul,Finset.sum_powerset_neg_one_pow_card]
      have he : V.filter (fun v => q ≤ sep v) = ∅ ↔ q = p := by
        constructor
        · intro hz
          by_contra hne
          obtain ⟨v,hv,hqv⟩ := hcover q hqp hne
          have hm : v ∈ V.filter (fun v => q ≤ sep v) := Finset.mem_filter.mpr ⟨hv,hqv⟩
          rw [hz] at hm
          exact Finset.not_mem_empty v hm
        · intro h
          subst q
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hpv
          exact (not_le_of_gt (hproper v hv)) hpv
      by_cases hq : q = p
      · rw [if_pos (he.mpr hq),if_pos hq,one_mul]
      · rw [if_neg (fun hz => hq (he.mp hz)),if_neg hq,zero_mul]
    · have hne : q ≠ p := fun he => hqp (he ▸ le_refl p)
      simp [hqp,hne]
  simp_rw [hinner]
  simp

theorem separating_powerset_incidence {α : Type*} [Fintype α]
    [SemilatticeInf α] [OrderTop α] (f : α → Int) (p : α) (V : Finset α)
    (hproper : ∀ v ∈ V, v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ v) :
    (∑ S ∈ V.powerset, (-1 : Int)^S.card * lowerIncidence f (p ⊓ S.inf id)) = f p :=
  separating_map_powerset_incidence f p V id hproper hcover

noncomputable def properRefinements {n : Nat} (p : ColorPattern n) : Finset (ColorPattern n) :=
  Finset.univ.filter (· < p)

noncomputable def indexedCoarseningFacet {n : Nat} {β : Type*}
    (V : Finset β) (sep : β → ColorPattern n) (c : ColorPattern n) : Finset β :=
  V.filter (fun v => c ≤ sep v)

noncomputable def indexedCertificateCoarseningFacets {n : Nat} {β : Type*} [DecidableEq β]
    (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n) : Finset (Finset β) :=
  (Finset.univ.filter (fun c => CertificateConstraint c ∧ c ≤ p)).image (indexedCoarseningFacet V sep)

/-- Faces are exactly subsets whose common refinement remains winning. -/
theorem indexedCertificateCoarseningFaces_eq {n : Nat} {β : Type*} [DecidableEq β]
    (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n) :
    facetFaces (indexedCertificateCoarseningFacets p V sep) =
      V.powerset.filter (fun S => WinningColorPattern (p ⊓ S.inf sep)) := by
  classical
  ext S
  simp only [mem_facetFaces,indexedCertificateCoarseningFacets,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powerset,
    winning_iff_constraint_refinement,le_inf_iff,Finset.le_inf_iff]
  constructor
  · rintro ⟨_,⟨c,⟨hc,hcp⟩,rfl⟩,hS⟩
    refine ⟨fun v hv => (Finset.mem_filter.mp (hS hv)).1,c,hc,hcp,?_⟩
    intro v hv
    exact (Finset.mem_filter.mp (hS hv)).2
  · rintro ⟨hSV,c,hc,hcp,hcS⟩
    exact ⟨indexedCoarseningFacet V sep c,⟨c,⟨hc,hcp⟩,rfl⟩,
      fun v hv => Finset.mem_filter.mpr ⟨hSV hv,hcS v hv⟩⟩

/-- General ORIGINAL-game coefficient/Euler bridge with independently indexed
separators. Duplicate separator values do not require an injectivity assumption. -/
theorem winningJoinCoefficient_eq_indexed_face_sum {n : Nat} {β : Type*} [DecidableEq β]
    (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v) :
    winningJoinCoefficient n p =
      faceAlternatingSum (facetFaces (indexedCertificateCoarseningFacets p V sep)) := by
  classical
  rw [indexedCertificateCoarseningFaces_eq]
  have hs := separating_map_powerset_incidence (winningJoinCoefficient n) p V sep hproper hcover
  simp_rw [winningJoinCoefficient_incidence] at hs
  unfold faceAlternatingSum
  rw [Finset.sum_filter]
  symm
  simpa only [mul_ite,mul_one,mul_zero] using hs

noncomputable def coarseningFacet {n : Nat} (V : Finset (ColorPattern n))
    (c : ColorPattern n) : Finset (ColorPattern n) := indexedCoarseningFacet V id c

noncomputable def certificateCoarseningFacets {n : Nat} (p : ColorPattern n)
    (V : Finset (ColorPattern n)) : Finset (Finset (ColorPattern n)) :=
  indexedCertificateCoarseningFacets p V id

theorem certificateCoarseningFaces_eq {n : Nat} (p : ColorPattern n)
    (V : Finset (ColorPattern n)) :
    facetFaces (certificateCoarseningFacets p V) =
      V.powerset.filter (fun S => WinningColorPattern (p ⊓ S.inf id)) :=
  indexedCertificateCoarseningFaces_eq p V id

theorem winningJoinCoefficient_eq_coarsening_face_sum {n : Nat} (p : ColorPattern n)
    (V : Finset (ColorPattern n)) (hproper : ∀ v ∈ V, v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ v) :
    winningJoinCoefficient n p =
      faceAlternatingSum (facetFaces (certificateCoarseningFacets p V)) :=
  winningJoinCoefficient_eq_indexed_face_sum p V id hproper hcover

/-- Canonical unconditional form for any original pattern, including empty and
losing instances. No all-five or connectedness assumption is used. -/
theorem winningJoinCoefficient_eq_proper_refinement_face_sum {n : Nat} (p : ColorPattern n) :
    winningJoinCoefficient n p =
      faceAlternatingSum (facetFaces (certificateCoarseningFacets p (properRefinements p))) := by
  apply winningJoinCoefficient_eq_coarsening_face_sum
  · intro v hv
    simpa [properRefinements] using hv
  · intro q hqp hne
    exact ⟨q,by simp [properRefinements,lt_of_le_of_ne hqp hne],le_rfl⟩

#print axioms separating_map_powerset_incidence
#print axioms winningJoinCoefficient_eq_proper_refinement_face_sum
end LC004

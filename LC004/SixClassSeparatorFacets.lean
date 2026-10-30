import LC004.LocalCertificateCatalogues
import LC004.IncidenceFaceSum

namespace LC004

/-- All unordered nontrivial two-part cuts of six points, represented with
rank zero on the true side. The omitted mask31 would be the trivial cut. -/
def sixCutBit (t : Fin 31) (u : Fin 6) : Bool :=
  if u = 0 then true else Nat.testBit t.val (u.val - 1)

def sixCutSeparator (t : Fin 31) : ColorPattern 6 := Setoid.ker (sixCutBit t)

theorem sixCut_nonconstant : ∀ t : Fin 31, ∃ u v, sixCutBit t u ≠ sixCutBit t v := by
  decide +kernel

theorem sixCut_complete : ∀ f : Fin 6 → Bool,
    (∃ u v, f u ≠ f v) → ∃ t : Fin 31, ∀ u v,
      (sixCutBit t u = sixCutBit t v ↔ f u = f v) := by
  decide +kernel

/-- The exact local facet associated with a noncrossing 2/3 certificate. -/
def sixCertificateCutFacet (s : Fin 8) : Finset (Fin 31) :=
  Finset.univ.filter (fun t => ∀ u v,
    localNC6Color s u = localNC6Color s v → sixCutBit t u = sixCutBit t v)

/-- A two-triple certificate lies below one cut. A three-pair certificate lies
below three cuts. Treating both as a single choice vertex loses this incidence. -/
theorem sixCertificateCutFacet_card : ∀ s : Fin 8,
    (sixCertificateCutFacet s).card = if s = 0 ∨ s = 1 ∨ s = 5 then 1 else 3 := by
  unfold sixCertificateCutFacet
  decide +kernel

theorem sixCutSeparator_strict (t : Fin 31) : sixCutSeparator t < (⊤ : ColorPattern 6) := by
  apply lt_of_le_of_ne le_top
  intro he
  obtain ⟨u,v,huv⟩ := sixCut_nonconstant t
  have hh : sixCutSeparator t u v := (Setoid.ext_iff.mp he u v).mpr trivial
  exact huv hh

theorem sixCutSeparators_cover (r : ColorPattern 6) (hne : r ≠ ⊤) :
    ∃ t : Fin 31, r ≤ sixCutSeparator t := by
  classical
  have hn : ¬ (⊤ : ColorPattern 6) ≤ r := fun h => hne (top_le_iff.mp h)
  rw [Setoid.le_def] at hn
  push_neg at hn
  obtain ⟨u,v,_,huv⟩ := hn
  let f : Fin 6 → Bool := fun w => decide (r u w)
  have hu : f u = true := by simp only [f,decide_eq_true_eq]; exact r.refl u
  have hv : f v = false := by simpa only [f,decide_eq_false_iff_not] using huv
  obtain ⟨t,ht⟩ := sixCut_complete f ⟨u,v,by rw [hu,hv]; decide⟩
  refine ⟨t,fun x y hxy => (ht x y).mpr ?_⟩
  simp only [f,decide_eq_decide]
  exact ⟨fun hux => r.trans hux hxy,fun huy => r.trans huy (r.symm hxy)⟩

theorem localNC6_catalogue_valid : ∀ s : Fin 8,
    SmallColor23 (localNC6Color s) ∧ NoncrossingColor (localNC6Color s) := by
  unfold SmallColor23 NoncrossingColor
  decide +kernel

theorem localNC6_catalogue_constraint (s : Fin 8) :
    CertificateConstraint (Setoid.ker (localNC6Color s)) := by
  constructor
  · intro u
    have he : patternClassPositions (Setoid.ker (localNC6Color s)) u =
        Finset.univ.filter (fun v => localNC6Color s u = localNC6Color s v) := by
      ext v
      simp only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    rw [he]
    exact (localNC6_catalogue_valid s).1 u
  · exact (localNC6_catalogue_valid s).2

theorem six_indexed_facets :
    indexedCertificateCoarseningFacets (⊤ : ColorPattern 6) Finset.univ sixCutSeparator =
      Finset.univ.image sixCertificateCutFacet := by
  classical
  have hg : Finset.univ.filter (fun c : ColorPattern 6 => CertificateConstraint c ∧ c ≤ ⊤) =
      Finset.univ.image (fun s : Fin 8 => Setoid.ker (localNC6Color s)) := by
    ext c
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,le_top,and_true,Finset.mem_image]
    constructor
    · intro hc
      obtain ⟨s,hs⟩ := localNC6_pattern_complete c hc.1 hc.2
      exact ⟨s,hs.symm⟩
    · rintro ⟨s,rfl⟩
      exact localNC6_catalogue_constraint s
  unfold indexedCertificateCoarseningFacets
  rw [hg,Finset.image_image]
  apply Finset.image_congr
  intro s _
  ext t
  simp only [Function.comp_apply,indexedCoarseningFacet,Finset.mem_filter,Finset.mem_univ,true_and,
    sixCertificateCutFacet]
  rfl

/-- Kernel evaluation of the small 31-vertex complex; facets have size one or
three, with duplicates and empty faces handled by finite-set operations. -/
theorem six_local_face_sum :
    faceAlternatingSum (facetFaces (Finset.univ.image sixCertificateCutFacet)) = -1 := by
  decide +kernel

/-- A positive original-game coefficient evaluation using the new six-point
separator structure, rather than a compressed choice-complex assumption. -/
theorem winningJoinCoefficient_single_six :
    winningJoinCoefficient 6 (⊤ : ColorPattern 6) = -1 := by
  rw [winningJoinCoefficient_eq_indexed_face_sum (⊤ : ColorPattern 6) Finset.univ sixCutSeparator
    (fun t _ => sixCutSeparator_strict t)
    (fun r _ hn => by obtain ⟨t,ht⟩ := sixCutSeparators_cover r hn; exact ⟨t,Finset.mem_univ t,ht⟩)]
  rw [six_indexed_facets]
  exact six_local_face_sum

#print axioms sixCertificateCutFacet_card
#print axioms winningJoinCoefficient_single_six
end LC004

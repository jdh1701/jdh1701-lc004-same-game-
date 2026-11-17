import LC004.IncidenceFaceSum

namespace LC004
open scoped Classical

/-- Extend a Boolean cut of one original class constantly over all other classes. -/
noncomputable def classCutColor {n : Nat} (p : ColorPattern n)
    (a : Fin n) (f : Fin n → Bool) (x : Fin n) : Bool :=
  if p a x then f x else false

noncomputable def classBinaryCut {n : Nat} (p : ColorPattern n)
    (a : Fin n) (f : Fin n → Bool) : ColorPattern n :=
  p ⊓ Setoid.ker (classCutColor p a f)

def ClassCutNonconstant {n : Nat} (p : ColorPattern n)
    (a : Fin n) (f : Fin n → Bool) : Prop :=
  ∃ u v, p a u ∧ p a v ∧ f u ≠ f v

/-- All nontrivial cuts of individual classes, with equal separators deduplicated.
This is much smaller than the family of all proper refinements in general. -/
noncomputable def classCutSeparators {n : Nat} (p : ColorPattern n) :
    Finset (ColorPattern n) :=
  (Finset.univ.filter (fun af : Fin n × (Fin n → Bool) =>
    ClassCutNonconstant p af.1 af.2)).image (fun af => classBinaryCut p af.1 af.2)

theorem classBinaryCut_strict {n : Nat} (p : ColorPattern n)
    (a : Fin n) (f : Fin n → Bool) (hf : ClassCutNonconstant p a f) :
    classBinaryCut p a f < p := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  obtain ⟨u,v,hu,hv,huv⟩ := hf
  have hp : p u v := p.trans (p.symm hu) hv
  have hh := ((Setoid.ext_iff.mp he u v).mpr hp).2
  change classCutColor p a f u = classCutColor p a f v at hh
  exact huv (by simpa only [classCutColor,if_pos hu,if_pos hv] using hh)

theorem classCutSeparators_strict {n : Nat} (p : ColorPattern n) :
    ∀ q ∈ classCutSeparators p, q < p := by
  intro q hq
  obtain ⟨⟨a,f⟩,haf,rfl⟩ := Finset.mem_image.mp hq
  exact classBinaryCut_strict p a f (Finset.mem_filter.mp haf).2

/-- Every proper refinement is separated by a binary cut of just one original
class. This works for arbitrary patterns, including all mixed profiles. -/
theorem classCutSeparators_cover {n : Nat} (p : ColorPattern n)
    (r : ColorPattern n) (hrp : r ≤ p) (hne : r ≠ p) :
    ∃ q ∈ classCutSeparators p, r ≤ q := by
  classical
  have hn : ¬ p ≤ r := fun h => hne (le_antisymm hrp h)
  rw [Setoid.le_def] at hn
  push_neg at hn
  obtain ⟨a,b,hab,hnab⟩ := hn
  let f : Fin n → Bool := fun x => decide (r a x)
  have hfa : f a = true := by simp only [f,decide_eq_true_eq]; exact r.refl a
  have hfb : f b = false := by simpa only [f,decide_eq_false_iff_not] using hnab
  have hnc : ClassCutNonconstant p a f :=
    ⟨a,b,p.refl a,hab,by rw [hfa,hfb]; decide⟩
  refine ⟨classBinaryCut p a f,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨(a,f),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnc⟩,rfl⟩
  · intro x y hxy
    refine ⟨hrp hxy,?_⟩
    change classCutColor p a f x = classCutColor p a f y
    by_cases hx : p a x
    · have hy : p a y := p.trans hx (hrp hxy)
      simp only [classCutColor,if_pos hx,if_pos hy,f,decide_eq_decide]
      exact ⟨fun h => r.trans h hxy,fun h => r.trans h (r.symm hxy)⟩
    · have hy : ¬ p a y := fun h => hx (p.trans h (p.symm (hrp hxy)))
      simp only [classCutColor,if_neg hx,if_neg hy]

/-- The ORIGINAL coefficient uses only binary cuts within individual classes;
no all-five, noncrossing, connectivity or bounded-profile assumption is needed. -/
theorem winningJoinCoefficient_eq_class_cut_face_sum {n : Nat} (p : ColorPattern n) :
    winningJoinCoefficient n p =
      faceAlternatingSum (facetFaces (certificateCoarseningFacets p (classCutSeparators p))) :=
  winningJoinCoefficient_eq_coarsening_face_sum p (classCutSeparators p)
    (classCutSeparators_strict p) (classCutSeparators_cover p)

#print axioms classCutSeparators_cover
#print axioms winningJoinCoefficient_eq_class_cut_face_sum
end LC004

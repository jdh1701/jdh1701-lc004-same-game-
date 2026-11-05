import LC004.FiveClassRefinementEquiv

namespace LC004
open scoped Classical

noncomputable def fivePatternFiberEquiv {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) (q : Quotient p) :
    {x : Fin n // Quotient.mk p x = q} ≃ Fin 5 :=
  (Equiv.subtypeEquivRight (fun x => (mem_patternQuotientFiber p q x).symm)).trans
    ((patternQuotientFiber p q).orderIsoOfFin (by
      rw [patternQuotientFiber_eq_class]
      exact hfive q.out)).toEquiv.symm

noncomputable def fivePatternQuotientCoordinates {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    Fin n ≃ Quotient p × Fin 5 :=
  (Equiv.sigmaFiberEquiv (Quotient.mk p)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fivePatternFiberEquiv p hfive))

noncomputable def fivePatternCoordinates {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    Fin n ≃ Fin (Fintype.card (Quotient p)) × Fin 5 :=
  (fivePatternQuotientCoordinates p hfive).trans
    (Equiv.prodCongr (Fintype.equivFin (Quotient p)) (Equiv.refl _))

theorem fivePatternCoordinates_fst {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) (x : Fin n) :
    (fivePatternCoordinates p hfive x).1 = Fintype.equivFin (Quotient p) (Quotient.mk p x) := rfl

theorem fivePatternCoordinates_base {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    p = Setoid.comap (fivePatternCoordinates p hfive)
      (fiveClassBaseSetoid (Fintype.card (Quotient p))) := by
  apply Setoid.ext
  intro x y
  change p x y ↔ (fivePatternCoordinates p hfive x).1 = (fivePatternCoordinates p hfive y).1
  rw [fivePatternCoordinates_fst,fivePatternCoordinates_fst,
    (Fintype.equivFin (Quotient p)).injective.eq_iff]
  exact Quotient.eq.symm

/-- Relabeling positions preserves exact class cardinalities. -/
theorem setoidClassFinset_comap_card {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (r : Setoid β) (u : α) :
    (setoidClassFinset (Setoid.comap e r) u).card = (setoidClassFinset r (e u)).card := by
  classical
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv
    simpa only [setoidClassFinset,Finset.mem_filter,Finset.mem_univ,true_and,
      Setoid.comap_rel] using hv
  · intro v _ w _ h
    exact e.injective h
  · intro v hv
    exact ⟨e.symm v,by simpa [setoidClassFinset,Setoid.comap_rel] using hv,e.apply_symm_apply v⟩

theorem setoidSmallClasses23_comap_iff {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (r : Setoid β) :
    SetoidSmallClasses23 (Setoid.comap e r) ↔ SetoidSmallClasses23 r := by
  constructor
  · intro h v
    have hh := h (e.symm v)
    simpa only [setoidClassFinset_comap_card,e.apply_symm_apply] using hh
  · intro h u
    simp only [setoidClassFinset_comap_card]
    exact h (e u)

theorem setoid_comap_equiv_injective {α β : Type*} (e : α ≃ β) :
    Function.Injective (Setoid.comap (e : α → β)) := by
  intro r s h
  apply Setoid.ext
  intro u v
  have hh := Setoid.ext_iff.mp h (e.symm u) (e.symm v)
  simpa only [Setoid.comap_rel,e.apply_symm_apply] using hh

theorem setoid_comap_equiv_cancel {α β : Type*} (e : α ≃ β) (r : Setoid α) :
    Setoid.comap e (Setoid.comap e.symm r) = r := by
  apply Setoid.ext
  intro u v
  simp only [Setoid.comap_rel,e.symm_apply_apply]

theorem setoid_comap_equiv_le_iff {α β : Type*} (e : α ≃ β) (r s : Setoid β) :
    Setoid.comap e r ≤ Setoid.comap e s ↔ r ≤ s := by
  constructor
  · intro h u v huv
    have hx : Setoid.comap e r (e.symm u) (e.symm v) := by
      simpa only [Setoid.comap_rel,e.apply_symm_apply] using huv
    have hy := h hx
    simpa only [Setoid.comap_rel,e.apply_symm_apply] using hy
  · intro h u v huv
    exact h huv

/-- The inverse representation for any original all-five pattern, with no
assumption about a pre-existing coordinate model. -/
theorem five_original_small_refinement_unique {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (c : ColorPattern n) (hcp : c ≤ p) (hc : SetoidSmallClasses23 c) :
    ∃! a : Fin (Fintype.card (Quotient p)) → Fin 10,
      c = Setoid.comap (fivePatternCoordinates p hfive) (fiveAssignmentSetoid a) := by
  let e := fivePatternCoordinates p hfive
  let r := Setoid.comap e.symm c
  have hr : r ≤ fiveClassBaseSetoid (Fintype.card (Quotient p)) := by
    intro u v huv
    have hh := hcp huv
    have hx := (Setoid.ext_iff.mp (fivePatternCoordinates_base p hfive) (e.symm u) (e.symm v)).mp hh
    change fiveClassBaseSetoid _ (e (e.symm u)) (e (e.symm v)) at hx
    simpa only [e.apply_symm_apply] using hx
  have hs : SetoidSmallClasses23 r := (setoidSmallClasses23_comap_iff e.symm c).mpr hc
  obtain ⟨a,ha,_⟩ := five_small_refinement_unique_assignment r hr hs
  have he : c = Setoid.comap e (fiveAssignmentSetoid a) := by
    apply Setoid.ext
    intro u v
    have hh := Setoid.ext_iff.mp ha (e u) (e v)
    simpa only [r,Setoid.comap_rel,Equiv.symm_apply_apply] using hh
  refine ⟨a,he,?_⟩
  intro b hb
  exact fiveAssignmentSetoid_injective
    (setoid_comap_equiv_injective e (hb.symm.trans he))

/-- Every encoded tuple has the required pair/triple class sizes. -/
theorem five_encoded_small_classes {n k : Nat} (e : Fin n ≃ Fin k × Fin 5)
    (a : Fin k → Fin 10) : SetoidSmallClasses23 (Setoid.comap e (fiveAssignmentSetoid a)) :=
  (setoidSmallClasses23_comap_iff e _).mpr (fiveAssignmentSetoid_small a)

#print axioms fivePatternCoordinates_base
#print axioms five_original_small_refinement_unique
end LC004

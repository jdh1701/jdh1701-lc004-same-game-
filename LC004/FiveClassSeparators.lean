import LC004.FiveCertificateGeneratorEquiv

namespace LC004
open scoped Classical

abbrev FiveCut := Fin 5 ⊕ Fin 10

def fiveCutBit : FiveCut → Fin 5 → Bool
  | .inl u, v => decide (v = u)
  | .inr s, v => fiveSplitBit s v

theorem fiveCut_complete : ∀ f : Fin 5 → Bool,
    (∃ u v, f u ≠ f v) → ∃ t : FiveCut, ∀ u v,
      (fiveCutBit t u = fiveCutBit t v ↔ f u = f v) := by decide +kernel

theorem fiveCut_nonconstant : ∀ t : FiveCut, ∃ u v,
    fiveCutBit t u ≠ fiveCutBit t v := by decide +kernel

theorem fiveSplit_le_cut_iff : ∀ s : Fin 10, ∀ t : FiveCut,
    (∀ u v, fiveSplitBit s u = fiveSplitBit s v → fiveCutBit t u = fiveCutBit t v) ↔
      t = Sum.inr s := by decide +kernel

def fiveCutSeparator {k : Nat} (i : Fin k) (t : FiveCut) : Setoid (Fin k × Fin 5) :=
  Setoid.ker (fun u => (u.1,if u.1 = i then fiveCutBit t u.2 else false))

theorem fiveCutSeparator_le_base {k : Nat} (i : Fin k) (t : FiveCut) :
    fiveCutSeparator i t ≤ fiveClassBaseSetoid k := by
  intro u v h
  change (u.1,_) = (v.1,_) at h
  change u.1 = v.1
  exact congrArg (fun z : Fin k × Bool => z.1) h

theorem fiveCutSeparator_lt_base {k : Nat} (i : Fin k) (t : FiveCut) :
    fiveCutSeparator i t < fiveClassBaseSetoid k := by
  apply lt_of_le_of_ne (fiveCutSeparator_le_base i t)
  intro he
  obtain ⟨u,v,huv⟩ := fiveCut_nonconstant t
  have hb : fiveClassBaseSetoid k (i,u) (i,v) := rfl
  have hs := (Setoid.ext_iff.mp he (i,u) (i,v)).mpr hb
  exact huv (by simpa only [fiveCutSeparator,Setoid.ker_def,if_pos rfl,Prod.mk.injEq,true_and] using hs)

theorem fiveAssignment_le_separator_iff {k : Nat} (a : Fin k → Fin 10)
    (i : Fin k) (t : FiveCut) :
    fiveAssignmentSetoid a ≤ fiveCutSeparator i t ↔ t = Sum.inr (a i) := by
  constructor
  · intro h
    apply (fiveSplit_le_cut_iff (a i) t).mp
    intro u v huv
    have ha : fiveAssignmentSetoid a (i,u) (i,v) := Prod.ext rfl huv
    have hs := h ha
    simpa only [fiveCutSeparator,Setoid.ker_def,if_pos rfl,Prod.mk.injEq,true_and] using hs
  · intro ht
    subst t
    rintro ⟨j,u⟩ ⟨l,v⟩ h
    change (j,fiveSplitBit (a j) u) = (l,fiveSplitBit (a l) v) at h
    have hjl : j = l := congrArg Prod.fst h
    subst l
    by_cases hji : j = i
    · subst j
      simpa only [fiveCutSeparator,Setoid.ker_def,if_pos rfl,fiveCutBit] using h
    · change (j,if j = i then _ else false) = (j,if j = i then _ else false)
      simp only [hji,if_false]

/-- The fifteen possible two-block cuts in each class separate EVERY proper
refinement, including refinements with singleton blocks. -/
theorem fiveCutSeparators_cover {k : Nat} (r : Setoid (Fin k × Fin 5))
    (hr : r ≤ fiveClassBaseSetoid k) (hne : r ≠ fiveClassBaseSetoid k) :
    ∃ i : Fin k, ∃ t : FiveCut, r ≤ fiveCutSeparator i t := by
  classical
  have hnb : ¬ fiveClassBaseSetoid k ≤ r := fun h => hne (le_antisymm hr h)
  rw [Setoid.le_def] at hnb
  push_neg at hnb
  obtain ⟨⟨i,u⟩,⟨j,v⟩,hbase,hnot⟩ := hnb
  change i = j at hbase
  subst j
  let f : Fin 5 → Bool := fun w => decide (r (i,u) (i,w))
  have hfu : f u = true := by simp only [f,decide_eq_true_eq]; exact r.refl _
  have hfv : f v = false := by simpa only [f,decide_eq_false_iff_not] using hnot
  obtain ⟨t,ht⟩ := fiveCut_complete f ⟨u,v,by rw [hfu,hfv]; decide⟩
  refine ⟨i,t,?_⟩
  rintro ⟨j,x⟩ ⟨l,y⟩ h
  have hjl : j = l := hr h
  subst l
  by_cases hji : j = i
  · subst j
    have hfe : f x = f y := by
      simp only [f,decide_eq_decide]
      exact ⟨fun hux => r.trans hux h,fun huy => r.trans huy (r.symm h)⟩
    have hh : (i,fiveCutBit t x) = (i,fiveCutBit t y) := Prod.ext rfl ((ht x y).mpr hfe)
    simpa only [fiveCutSeparator,Setoid.ker_def,if_pos rfl] using hh
  · change (j,if j = i then _ else false) = (j,if j = i then _ else false)
    simp only [hji,if_false]

noncomputable def fiveOriginalSeparator {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (v : Fin (Fintype.card (Quotient p)) × FiveCut) : ColorPattern n :=
  Setoid.comap (fivePatternCoordinates p hfive) (fiveCutSeparator v.1 v.2)

/-- The original game's interval has a concrete separating family with only
fifteen vertices per class. No coatom classification is assumed. -/
theorem fiveOriginalSeparators_strict {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (v : Fin (Fintype.card (Quotient p)) × FiveCut) : fiveOriginalSeparator p hfive v < p := by
  let e := fivePatternCoordinates p hfive
  have hle : fiveOriginalSeparator p hfive v ≤ p := by
    intro x y hxy
    apply (Setoid.ext_iff.mp (fivePatternCoordinates_base p hfive) x y).mpr
    exact fiveCutSeparator_le_base v.1 v.2 hxy
  apply lt_of_le_of_ne hle
  intro he
  have hx : Setoid.comap e (fiveCutSeparator v.1 v.2) =
      Setoid.comap e (fiveClassBaseSetoid _) := he.trans (fivePatternCoordinates_base p hfive)
  exact (ne_of_lt (fiveCutSeparator_lt_base v.1 v.2)) (setoid_comap_equiv_injective e hx)

theorem fiveOriginalSeparators_cover {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (q : ColorPattern n) (hqp : q ≤ p) (hne : q ≠ p) :
    ∃ v : Fin (Fintype.card (Quotient p)) × FiveCut, q ≤ fiveOriginalSeparator p hfive v := by
  let e := fivePatternCoordinates p hfive
  let r := Setoid.comap e.symm q
  have hr : r ≤ fiveClassBaseSetoid (Fintype.card (Quotient p)) := by
    intro u v huv
    have hh := (Setoid.ext_iff.mp (fivePatternCoordinates_base p hfive) (e.symm u) (e.symm v)).mp
      (hqp huv)
    change fiveClassBaseSetoid _ (e (e.symm u)) (e (e.symm v)) at hh
    simpa only [e.apply_symm_apply] using hh
  have hnr : r ≠ fiveClassBaseSetoid _ := by
    intro he
    apply hne
    calc
      q = Setoid.comap e r := (setoid_comap_equiv_cancel e q).symm
      _ = Setoid.comap e (fiveClassBaseSetoid _) := congrArg (Setoid.comap e) he
      _ = p := (fivePatternCoordinates_base p hfive).symm
  obtain ⟨i,t,ht⟩ := fiveCutSeparators_cover r hr hnr
  refine ⟨(i,t),?_⟩
  have hh := (setoid_comap_equiv_le_iff e r (fiveCutSeparator i t)).mpr ht
  change Setoid.comap e (Setoid.comap e.symm q) ≤ fiveOriginalSeparator p hfive (i,t) at hh
  rw [setoid_comap_equiv_cancel] at hh
  exact hh

#print axioms fiveCutSeparators_cover
end LC004

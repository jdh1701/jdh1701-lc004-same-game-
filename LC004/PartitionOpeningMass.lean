import LC004.IntrinsicDiagonalProfiles

namespace LC004
open scoped BigOperators

/-- A class has a canonical least position, independent of quotient.out. -/
noncomputable def patternClassMinimum {n : Nat} (p : ColorPattern n)
    (q : Quotient p) : Fin n := by
  classical
  exact (patternQuotientFiber p q).min' ⟨q.out, by
    simp only [patternQuotientFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Quotient.out_eq]⟩

theorem patternClassMinimum_mem {n : Nat} (p : ColorPattern n) (q : Quotient p) :
    patternClassMinimum p q ∈ patternQuotientFiber p q := by
  classical
  exact Finset.min'_mem _ _

theorem patternClassMinimum_quotient {n : Nat} (p : ColorPattern n) (q : Quotient p) :
    Quotient.mk p (patternClassMinimum p q) = q := by
  classical
  exact (Finset.mem_filter.mp (patternClassMinimum_mem p q)).2

theorem patternClassMinimum_injective {n : Nat} (p : ColorPattern n) :
    Function.Injective (patternClassMinimum p) := by
  intro q r h
  have he := congrArg (Quotient.mk p) h
  simpa only [patternClassMinimum_quotient] using he

theorem patternClassMinimum_le {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternClassMinimum p (Quotient.mk p i) ≤ i := by
  classical
  exact Finset.min'_le _ i (by
    simp only [patternQuotientFiber, Finset.mem_filter, Finset.mem_univ, true_and])

noncomputable def patternOpenedClasses {n : Nat} (p : ColorPattern n)
    (cut : Nat) : Finset (Quotient p) := by
  classical
  exact Finset.univ.filter (fun q => (patternClassMinimum p q).val < cut)

/-- Total sizes of classes whose first position precedes a cut. This is
the cumulative degree that will enter a rooted-tree word encoding. -/
noncomputable def patternOpeningMass {n : Nat} (p : ColorPattern n) (cut : Nat) : Nat := by
  classical
  exact ∑ q ∈ patternOpenedClasses p cut, (patternQuotientFiber p q).card

/-- Class selection has its expected size without any assumptions on
block sizes or noncrossing. -/
open scoped Classical in
theorem selected_pattern_positions_card {n : Nat} (p : ColorPattern n)
    (chosen : Finset (Quotient p)) :
    (selectedPatternPositions p chosen).card =
      ∑ q ∈ chosen, (patternQuotientFiber p q).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Quotient.mk p)
    (s := selectedPatternPositions p chosen) (t := chosen)
    (fun i hi => (Finset.mem_filter.mp hi).2)]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  ext i
  simp only [selectedPatternPositions, patternQuotientFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨by simpa only [h] using hq, h⟩⟩

/-- Every prefix position belongs to a class opened within that prefix.
Consequently the cumulative block degree dominates the prefix length.
This holds for all partitions; injective reconstruction will require NC. -/
theorem patternOpeningMass_prefix {n : Nat} (p : ColorPattern n) (cut : Nat)
    (hcut : cut ≤ n) : cut ≤ patternOpeningMass p cut := by
  classical
  let f : Fin cut → ↥(selectedPatternPositions p (patternOpenedClasses p cut)) :=
    fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hcut⟩, by
      simp only [selectedPatternPositions, patternOpenedClasses, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hle := patternClassMinimum_le p ⟨i.val, lt_of_lt_of_le i.isLt hcut⟩
      have hval : (patternClassMinimum p (Quotient.mk p
          ⟨i.val, lt_of_lt_of_le i.isLt hcut⟩)).val ≤ i.val := hle
      exact lt_of_le_of_lt hval i.isLt⟩
  have hinj : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun x : ↥(selectedPatternPositions p
      (patternOpenedClasses p cut)) => x.val.val) h)
  have h := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at h
  rw [selected_pattern_positions_card] at h
  exact h

theorem patternOpeningMass_total {n : Nat} (p : ColorPattern n) :
    patternOpeningMass p n = n := by
  classical
  have hclasses : patternOpenedClasses p n = Finset.univ := by
    ext q
    simp only [patternOpenedClasses, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (patternClassMinimum p q).isLt
  change (∑ q ∈ patternOpenedClasses p n, (patternQuotientFiber p q).card) = n
  rw [hclasses]
  exact (pattern_sum_class_sizes p).symm

#print axioms patternClassMinimum_injective
#print axioms patternOpeningMass_prefix
#print axioms patternOpeningMass_total

end LC004

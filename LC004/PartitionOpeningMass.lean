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

open scoped Classical in
/-- Class selection has its expected size without any assumptions on
block sizes or noncrossing. -/
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

/-- Place each class size at its least position, and zero elsewhere. -/
noncomputable def patternOpeningDegree {n : Nat} (p : ColorPattern n) (i : Fin n) : Nat := by
  classical
  exact ∑ q ∈ (Finset.univ : Finset (Quotient p)).filter
    (fun q => patternClassMinimum p q = i), (patternQuotientFiber p q).card

theorem patternOpeningDegree_at_minimum {n : Nat} (p : ColorPattern n)
    (q : Quotient p) : patternOpeningDegree p (patternClassMinimum p q) =
      (patternQuotientFiber p q).card := by
  classical
  unfold patternOpeningDegree
  apply Finset.sum_eq_single q
  · intro r hr hne
    have hmin := (Finset.mem_filter.mp hr).2
    exact (hne (patternClassMinimum_injective p hmin)).elim
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

theorem patternOpeningDegree_eq {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternOpeningDegree p i =
      if patternClassMinimum p (Quotient.mk p i) = i then
        (patternClassPositions p i).card else 0 := by
  classical
  split_ifs with hi
  · have h := patternOpeningDegree_at_minimum p (Quotient.mk p i)
    rw [hi, patternQuotientFiber_mk_eq_class] at h
    exact h
  · unfold patternOpeningDegree
    apply Finset.sum_eq_zero
    intro q hq
    have hmin := (Finset.mem_filter.mp hq).2
    have hqi : Quotient.mk p i = q := by
      rw [← hmin, patternClassMinimum_quotient]
    exact (hi (by simpa only [hqi] using hmin)).elim

theorem nonzero_patternOpeningDegree_minimum {n : Nat} (p : ColorPattern n)
    (i : Fin n) (hi : patternOpeningDegree p i ≠ 0) :
    patternClassMinimum p (Quotient.mk p i) = i := by
  by_contra h
  exact hi (by rw [patternOpeningDegree_eq, if_neg h])

/-- Positive arities in the degree encoding correspond to classes of
that size, with no multiplicity from block ordering or labels. -/
noncomputable def patternDegreeClassEquiv {n : Nat} (p : ColorPattern n)
    (s : Nat) (hs : 0 < s) :
    {q : Quotient p // (patternQuotientFiber p q).card = s} ≃
      {i : Fin n // patternOpeningDegree p i = s} where
  toFun q := ⟨patternClassMinimum p q.val,
    (patternOpeningDegree_at_minimum p q.val).trans q.property⟩
  invFun i := ⟨Quotient.mk p i.val, by
    have hne : patternOpeningDegree p i.val ≠ 0 := by rw [i.property]; omega
    have hmin := nonzero_patternOpeningDegree_minimum p i.val hne
    have h := patternOpeningDegree_at_minimum p (Quotient.mk p i.val)
    rw [hmin] at h
    exact h.symm.trans i.property⟩
  left_inv q := Subtype.ext (patternClassMinimum_quotient p q.val)
  right_inv i := Subtype.ext (nonzero_patternOpeningDegree_minimum p i.val (by rw [i.property]; omega))

open scoped Classical in
theorem patternOpeningDegree_arity_count {n : Nat} (p : ColorPattern n)
    (s : Nat) (hs : 0 < s) :
    Fintype.card {i : Fin n // patternOpeningDegree p i = s} =
      Fintype.card {q : Quotient p // (patternQuotientFiber p q).card = s} := by
  exact (Fintype.card_congr (patternDegreeClassEquiv p s hs)).symm

open scoped Classical in
theorem patternOpeningDegree_prefix_sum {n : Nat} (p : ColorPattern n) (cut : Nat) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < cut),
      patternOpeningDegree p i) = patternOpeningMass p cut := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Quotient p))
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < cut))
    (patternClassMinimum p) (fun q => (patternQuotientFiber p q).card)
  simpa only [patternOpeningDegree, patternOpeningMass, patternOpenedClasses,
    Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- A degree word with one terminal zero. For noncrossing partitions,
this is the intended bridge to rooted ordered trees. -/
noncomputable def patternTreeDegrees {n : Nat} (p : ColorPattern n) : List Nat :=
  List.ofFn (patternOpeningDegree p) ++ [0]

theorem patternTreeDegrees_length {n : Nat} (p : ColorPattern n) :
    (patternTreeDegrees p).length = n + 1 := by
  simp only [patternTreeDegrees, List.length_append, List.length_ofFn,
    List.length_singleton]

theorem patternTreeDegrees_sum {n : Nat} (p : ColorPattern n) :
    (patternTreeDegrees p).sum = n := by
  classical
  have h := patternOpeningDegree_prefix_sum p n
  have hf : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro i.isLt
  rw [hf, patternOpeningMass_total] at h
  simpa only [patternTreeDegrees, List.sum_append, List.sum_singleton,
    Nat.add_zero, List.sum_ofFn] using h

theorem patternTreeDegrees_prefix {n : Nat} (p : ColorPattern n) (cut : Nat)
    (hcut : cut ≤ n) : cut ≤ ((patternTreeDegrees p).take cut).sum := by
  rw [patternTreeDegrees, List.take_append_of_le_length
    (by simpa only [List.length_ofFn] using hcut), List.sum_take_ofFn,
    patternOpeningDegree_prefix_sum]
  exact patternOpeningMass_prefix p cut hcut

#print axioms patternOpeningDegree_arity_count
#print axioms patternTreeDegrees_sum
#print axioms patternTreeDegrees_prefix

#print axioms patternClassMinimum_injective
#print axioms patternOpeningMass_prefix
#print axioms patternOpeningMass_total

end LC004

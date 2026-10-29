import LC004.NoncrossingDegreeRealization
import LC004.CyclicWordEnumeration

namespace LC004
open scoped BigOperators

theorem patternOpeningDegree_le {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternOpeningDegree p i ≤ n := by
  classical
  rw [patternOpeningDegree_eq]
  split_ifs
  · exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq
      (by simp only [Finset.card_univ, Fintype.card_fin])
  · exact Nat.zero_le _

noncomputable def patternDegreeWord {n : Nat} (p : ColorPattern n) : CyclicDegreeWord n :=
  fun i => if h : i.val < n then
    ⟨patternOpeningDegree p ⟨i.val, h⟩, Nat.lt_succ_of_le (patternOpeningDegree_le p _)⟩ else 0

@[simp] theorem patternDegreeWord_castSucc {n : Nat} (p : ColorPattern n) (i : Fin n) :
    (patternDegreeWord p i.castSucc).val = patternOpeningDegree p i := by
  simp only [patternDegreeWord, Fin.val_castSucc, i.isLt, dite_true]

@[simp] theorem patternDegreeWord_last {n : Nat} (p : ColorPattern n) :
    patternDegreeWord p (Fin.last n) = 0 := by
  simp only [patternDegreeWord, Fin.val_last, lt_self_iff_false, dite_false]

open scoped Classical in
theorem patternDegreeWord_sum {n : Nat} (p : ColorPattern n) :
    ∑ i, (patternDegreeWord p i).val = n := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [patternDegreeWord_castSucc, patternDegreeWord_last, Fin.val_zero, Nat.add_zero]
  have h := patternOpeningDegree_prefix_sum p n
  have hf : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro i.isLt
  rw [hf, patternOpeningMass_total] at h
  exact h

theorem cyclicHeight_degreeWord {n : Nat} (w : CyclicDegreeWord n)
    (cut : Nat) (hcut : cut ≤ n) :
    cyclicHeight (degreeWordWeights w) cut =
      (degreePrefix (fun i => (w i).val) cut : Int) - cut := by
  classical
  have hf : ((Finset.univ : Finset (Fin (n + 1))).filter (fun i => i.val < cut)).card = cut := by
    have heq : (Finset.univ : Finset (Fin (n + 1))).filter (fun i => i.val < cut) =
        Finset.Iio (⟨cut, by omega⟩ : Fin (n + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
    rw [heq, Fin.card_Iio]
  simp only [cyclicHeight, degreeWordWeights, degreePrefix, Nat.cast_sum,
    Finset.sum_sub_distrib, Finset.sum_const, hf, nsmul_eq_mul, mul_one]

theorem rootedDegreeWord_iff {n : Nat} (w : CyclicDegreeWord n) :
    RootedDegreeWord w ↔ ∀ cut, cut ≤ n → cut ≤ degreePrefix (fun i => (w i).val) cut := by
  constructor
  · intro h cut hcut
    have h' := h cut (by omega)
    rw [cyclicHeight_degreeWord w cut hcut] at h'
    exact_mod_cast (show (cut : Int) ≤ (degreePrefix (fun i => (w i).val) cut : Int) by omega)
  · intro h cut hcut
    rw [cyclicHeight_degreeWord w cut (by omega)]
    have h' : (cut : Int) ≤ (degreePrefix (fun i => (w i).val) cut : Int) := by
      exact_mod_cast h cut (by omega)
    omega

theorem patternDegreeWord_rooted {n : Nat} (p : ColorPattern n) :
    RootedDegreeWord (patternDegreeWord p) := by
  apply rootedDegreeWord_iff.mpr
  intro cut hcut
  have h := degreePrefix_castLE (fun i => (patternDegreeWord p i).val)
    (Nat.le_succ n) cut hcut
  have heq : (fun i : Fin n => (patternDegreeWord p (Fin.castLE (Nat.le_succ n) i)).val) =
      patternOpeningDegree p := by
    funext i
    exact patternDegreeWord_castSucc p i
  rw [heq] at h
  rw [← h]
  change cut ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < cut),
    patternOpeningDegree p i
  rw [patternOpeningDegree_prefix_sum]
  exact patternOpeningMass_prefix p cut hcut

open scoped Classical in
theorem rootedDegreeWord_last_zero {n : Nat} (w : CyclicDegreeWord n)
    (hsum : ∑ i, (w i).val = n) (hroot : RootedDegreeWord w) :
    (w (Fin.last n)).val = 0 := by
  classical
  have hp := rootedDegreeWord_iff.mp hroot n (le_refl n)
  have h := degreePrefix_castLE (fun i => (w i).val) (Nat.le_succ n) n (le_refl n)
  rw [degreePrefix_total] at h
  rw [Fin.sum_univ_castSucc] at hsum
  change (∑ i : Fin n, (w i.castSucc).val) = degreePrefix (fun i => (w i).val) n at h
  omega

noncomputable def noncrossingDegreeWordEquiv (n : Nat) :
    {p : ColorPattern n // PatternNoncrossing p} ≃
      {w : CyclicDegreeWord n // (∑ i, (w i).val = n) ∧ RootedDegreeWord w} := by
  classical
  let f : {p : ColorPattern n // PatternNoncrossing p} →
      {w : CyclicDegreeWord n // (∑ i, (w i).val = n) ∧ RootedDegreeWord w} :=
    fun p => ⟨patternDegreeWord p.val, patternDegreeWord_sum p.val, patternDegreeWord_rooted p.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q heq
    apply Subtype.ext
    apply noncrossing_pattern_eq_of_opening_degree p.val q.val p.property q.property
    intro i
    have h := congrArg (fun w => (w.val i.castSucc).val) heq
    simpa only [f, patternDegreeWord_castSucc] using h
  · intro w
    let d : Fin n → Nat := fun i => (w.val i.castSucc).val
    have hlast := rootedDegreeWord_last_zero w.val w.property.1 w.property.2
    have hdSum : ∑ i, d i = n := by
      have h := w.property.1
      rw [Fin.sum_univ_castSucc, hlast, Nat.add_zero] at h
      exact h
    have hdPrefix : ∀ cut, cut ≤ n → cut ≤ degreePrefix d cut := by
      intro cut hcut
      have h := rootedDegreeWord_iff.mp w.property.2 cut hcut
      have heq := degreePrefix_castLE (fun i => (w.val i).val) (Nat.le_succ n) cut hcut
      rw [← heq] at h
      exact h
    obtain ⟨p, hp, hdegree⟩ := noncrossing_degree_realization n d hdSum hdPrefix
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    funext i
    apply Fin.ext
    cases i using Fin.lastCases with
    | last => simpa only [f, patternDegreeWord_last, Fin.val_zero] using hlast.symm
    | cast i => simpa only [f, patternDegreeWord_castSucc] using hdegree i

#print axioms noncrossingDegreeWordEquiv

end LC004

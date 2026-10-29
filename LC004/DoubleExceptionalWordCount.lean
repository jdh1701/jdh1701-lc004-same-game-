import LC004.SingleExceptionalWordCount

namespace LC004
open scoped BigOperators

def TailSingleExceptional {n : Nat} (f : Fin n → Nat) (a : Nat) : Prop :=
  ∃ j, f j = a ∧ ∀ t, t ≠ j → f t = 0 ∨ f t = 2

theorem doubleExceptionalWord_at_anchor {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (ha : 2 < a) (hzero : (w 0).val = a) :
    DoubleExceptionalWord w a ↔ TailSingleExceptional (fun j => (w j.succ).val) a := by
  classical
  constructor
  · rintro ⟨i, j, hij, hi, hj, hrest⟩
    have hi0j0 : i = 0 ∨ j = 0 := by
      by_contra h
      push_neg at h
      rcases hrest 0 (Ne.symm h.1) (Ne.symm h.2) with h | h <;> omega
    rcases hi0j0 with rfl | rfl
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨s, rfl⟩
      · exact (hij rfl).elim
      · refine ⟨s, hj, ?_⟩
        intro t hts
        exact hrest t.succ (Fin.succ_ne_zero _) (fun h => hts (Fin.succ_injective h))
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨s, rfl⟩
      · exact (hij rfl).elim
      · refine ⟨s, hi, ?_⟩
        intro t hts
        exact hrest t.succ (fun h => hts (Fin.succ_injective h)) (Fin.succ_ne_zero _)
  · rintro ⟨j, hj, hrest⟩
    refine ⟨0, j.succ, Ne.symm (Fin.succ_ne_zero _), hzero, hj, ?_⟩
    intro t ht0 htj
    rcases Fin.eq_zero_or_eq_succ t with h | ⟨s, rfl⟩
    · exact (ht0 h).elim
    · exact hrest s (fun h => htj (congrArg Fin.succ h))

open scoped Classical in
theorem tail_single_three_sum {n : Nat} (f : Fin n → Nat) (j : Fin n)
    (hj : f j = 3) (hrest : ∀ t, t ≠ j → f t = 0 ∨ f t = 2) :
    (∑ t, f t) = 3 + 2 * ((Finset.univ : Finset (Fin n)).filter (fun t => f t = 2)).card := by
  classical
  have hd (t : Fin n) : f t = (if t = j then 3 else 0) + (if f t = 2 then 2 else 0) := by
    by_cases ht : t = j
    · subst t
      rw [hj]
      norm_num
    · rcases hrest t ht with h | h <;> simp [ht, h]
  calc
    _ = (∑ t : Fin n, if t = j then 3 else 0) +
        ∑ t : Fin n, if f t = 2 then 2 else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => hd t)
    _ = 3 + 2 * ((Finset.univ : Finset (Fin n)).filter (fun t => f t = 2)).card := by
      rw [show (∑ t : Fin n, if t = j then 3 else 0) = 3 by simp]
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

noncomputable def anchoredTriplePosition {n : Nat} (w : CyclicDegreeWord n)
    (hw : DoubleExceptionalWord w 3) (hzero : (w 0).val = 3) : Fin n :=
  Classical.choose ((doubleExceptionalWord_at_anchor w 3 (by omega) hzero).mp hw)

theorem anchoredTriplePosition_spec {n : Nat} (w : CyclicDegreeWord n)
    (hw : DoubleExceptionalWord w 3) (hzero : (w 0).val = 3) :
    (w (anchoredTriplePosition w hw hzero).succ).val = 3 ∧
    ∀ t, t ≠ anchoredTriplePosition w hw hzero → (w t.succ).val = 0 ∨ (w t.succ).val = 2 :=
  Classical.choose_spec ((doubleExceptionalWord_at_anchor w 3 (by omega) hzero).mp hw)

open scoped Classical in
noncomputable def doubleAnchoredWordEquiv (k : Nat) (hk : 2 ≤ k) :
    {w : CyclicDegreeWord (2 * k + 2) //
      ((∑ i, (w i).val = 2 * k + 2) ∧ DoubleExceptionalWord w 3) ∧ (w 0).val = 3} ≃
    (Σ j : Fin (2 * k + 2), {s : Finset (Fin (2 * k + 2)) // s.card = k - 2 ∧ j ∉ s}) where
  toFun w :=
    let j := anchoredTriplePosition w.val w.property.1.2 w.property.2
    have hs := anchoredTriplePosition_spec w.val w.property.1.2 w.property.2
    ⟨j, ⟨Finset.univ.filter (fun t => (w.val t.succ).val = 2), by
      constructor
      · have hsum := tail_single_three_sum (fun t => (w.val t.succ).val) j hs.1 hs.2
        have ht := w.property.1.1
        rw [Fin.sum_univ_succ, w.property.2] at ht
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs.1]
        omega⟩⟩
  invFun x :=
    let j := x.1
    let s := x.2.val
    let w : CyclicDegreeWord (2 * k + 2) := Fin.cases ⟨3, by omega⟩
      (fun t => if t = j then ⟨3, by omega⟩ else if t ∈ s then ⟨2, by omega⟩ else 0)
    have hzero : (w 0).val = 3 := rfl
    have hj : (w j.succ).val = 3 := by simp only [w, Fin.cases_succ, if_pos rfl]
    have hrest : ∀ t, t ≠ j → (w t.succ).val = 0 ∨ (w t.succ).val = 2 := by
      intro t ht
      dsimp only [w, Fin.cases_succ]
      rw [if_neg ht]
      split_ifs <;> simp only [Fin.val_zero] <;> omega
    ⟨w, ⟨by
      rw [Fin.sum_univ_succ, hzero]
      have hs := tail_single_three_sum (fun t => (w t.succ).val) j hj hrest
      have hfilter : (Finset.univ : Finset (Fin (2 * k + 2))).filter
          (fun t => (w t.succ).val = 2) = s := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [w, Fin.cases_succ]
        by_cases ht : t = j
        · subst t
          simp only [if_pos rfl]
          have hnot := x.2.property.2
          change j ∉ s at hnot
          simp only [hnot, iff_false]
          omega
        · rw [if_neg ht]
          split_ifs <;> simp_all
      rw [hfilter, x.2.property.1] at hs
      omega,
      (doubleExceptionalWord_at_anchor w 3 (by omega) hzero).mpr ⟨j, hj, hrest⟩⟩, hzero⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    cases i using Fin.cases with
    | zero => exact w.property.2.symm
    | succ t =>
      have hs := anchoredTriplePosition_spec w.val w.property.1.2 w.property.2
      dsimp only
      simp only [Fin.cases_succ, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with ht htwo
      · exact hs.1.symm.trans (congrArg (fun t => (w.val t.succ).val) ht).symm
      · exact htwo.symm
      · rcases hs.2 t ht with hz | hz
        · exact hz.symm
        · exact (htwo hz).elim
  right_inv x := by
    classical
    rcases x with ⟨j, ⟨s, hcard, hnot⟩⟩
    let w : CyclicDegreeWord (2 * k + 2) := Fin.cases ⟨3, by omega⟩
      (fun t => if t = j then ⟨3, by omega⟩ else if t ∈ s then ⟨2, by omega⟩ else 0)
    have hz : (w 0).val = 3 := rfl
    have hj : (w j.succ).val = 3 := by simp only [w, Fin.cases_succ, if_pos rfl]
    have hrest : ∀ t, t ≠ j → (w t.succ).val = 0 ∨ (w t.succ).val = 2 := by
      intro t ht
      dsimp only [w, Fin.cases_succ]
      rw [if_neg ht]
      split_ifs <;> simp only [Fin.val_zero] <;> omega
    have hw : DoubleExceptionalWord w 3 :=
      (doubleExceptionalWord_at_anchor w 3 (by omega) hz).mpr ⟨j, hj, hrest⟩
    have hpos : anchoredTriplePosition w hw hz = j := by
      have hs := anchoredTriplePosition_spec w hw hz
      by_contra h
      rcases hs.2 j (Ne.symm h) with h | h <;> omega
    apply Sigma.ext hpos
    apply (Subtype.heq_iff_coe_eq (fun t => by dsimp only; rw [hpos])).mpr
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only
    simp only [Fin.cases_succ]
    by_cases ht : t = j
    · subst t
      simp only [if_pos rfl, hnot, iff_false]
      omega
    · rw [if_neg ht]
      split_ifs <;> simp_all

open scoped Classical in
theorem double_anchored_word_count (k : Nat) (hk : 2 ≤ k) :
    Fintype.card {w : CyclicDegreeWord (2 * k + 2) //
      ((∑ i, (w i).val = 2 * k + 2) ∧ DoubleExceptionalWord w 3) ∧ (w 0).val = 3} =
      (2 * k + 2) * (2 * k + 1).choose (k - 2) := by
  classical
  rw [Fintype.card_congr (doubleAnchoredWordEquiv k hk), Fintype.card_sigma]
  have hcard (j : Fin (2 * k + 2)) :
      Fintype.card {s : Finset (Fin (2 * k + 2)) // s.card = k - 2 ∧ j ∉ s} =
        (2 * k + 1).choose (k - 2) := by
    have hpred : ∀ s : Finset (Fin (2 * k + 2)),
        (s.card = k - 2 ∧ j ∉ s) ↔ s ∈ (Finset.univ.erase j).powersetCard (k - 2) := by
      intro s
      simp only [Finset.mem_powersetCard, Finset.subset_erase, Finset.subset_univ, and_true]
      exact and_comm
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hpred), Fintype.card_coe,
      Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

#print axioms double_anchored_word_count

end LC004

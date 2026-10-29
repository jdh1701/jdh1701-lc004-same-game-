import LC004.PartitionExceptionalWordProfiles

namespace LC004
open scoped BigOperators

theorem singleExceptionalWord_at_anchor {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (ha : 2 < a) (hzero : (w 0).val = a) :
    SingleExceptionalWord w a ↔ ∀ j : Fin n, (w j.succ).val = 0 ∨ (w j.succ).val = 2 := by
  constructor
  · rintro ⟨i, hi, hrest⟩
    have hi0 : i = 0 := by
      by_contra h
      rcases hrest 0 (Ne.symm h) with h | h <;> omega
    subst i
    intro j
    exact hrest j.succ (Fin.succ_ne_zero j)
  · intro hrest
    refine ⟨0, hzero, ?_⟩
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
    · exact (hj h).elim
    · exact hrest i

open scoped Classical in
theorem binary_vector_sum {n : Nat} (f : Fin n → Nat)
    (hf : ∀ i, f i = 0 ∨ f i = 2) :
    (∑ i, f i) = 2 * ((Finset.univ : Finset (Fin n)).filter (fun i => f i = 2)).card := by
  classical
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => f i = 2), 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rcases hf i with h | h <;> simp only [h] <;> norm_num
    _ = _ := by simp [Nat.mul_comm]

open scoped Classical in
noncomputable def singleSubsetDegreeWord (k : Nat) (hk : 1 ≤ k)
    (s : Finset (Fin (2 * k + 2))) : CyclicDegreeWord (2 * k + 2) :=
  Fin.cases (⟨4, by omega⟩ : Fin (2 * k + 2 + 1))
    (fun j : Fin (2 * k + 2) =>
      if j ∈ s then (⟨2, by omega⟩ : Fin (2 * k + 2 + 1)) else 0)

open scoped Classical in
noncomputable def singleAnchoredWordEquiv (k : Nat) (hk : 1 ≤ k) :
    {w : CyclicDegreeWord (2 * k + 2) //
      ((∑ i, (w i).val = 2 * k + 2) ∧ SingleExceptionalWord w 4) ∧ (w 0).val = 4} ≃
    {s : Finset (Fin (2 * k + 2)) // s.card = k - 1} where
  toFun w := ⟨Finset.univ.filter (fun j => (w.val j.succ).val = 2), by
    have hrest := (singleExceptionalWord_at_anchor w.val 4 (by omega) w.property.2).mp
      w.property.1.2
    have hs := binary_vector_sum (fun j => (w.val j.succ).val) hrest
    have ht := w.property.1.1
    rw [Fin.sum_univ_succ, w.property.2] at ht
    dsimp only at hs ht ⊢
    omega⟩
  invFun s :=
    let w := singleSubsetDegreeWord k hk s.val
    have hzero : (w 0).val = 4 := by rfl
    have hrest : ∀ j : Fin (2 * k + 2), (w j.succ).val = 0 ∨ (w j.succ).val = 2 := by
      intro j
      by_cases hj : j ∈ s.val
      · right; simp only [w, singleSubsetDegreeWord, Fin.cases_succ, if_pos hj]
      · left; simp only [w, singleSubsetDegreeWord, Fin.cases_succ, if_neg hj, Fin.val_zero]
    ⟨w, ⟨by
      rw [Fin.sum_univ_succ, hzero]
      have hs := binary_vector_sum (fun j => (w j.succ).val) hrest
      have hfilter : (Finset.univ : Finset (Fin (2 * k + 2))).filter
          (fun j => (w j.succ).val = 2) = s.val := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [w, singleSubsetDegreeWord, Fin.cases_succ]
        split_ifs <;> simp_all
      rw [hfilter, s.property] at hs
      dsimp only at hs ⊢
      omega,
      (singleExceptionalWord_at_anchor w 4 (by omega) hzero).mpr hrest⟩, hzero⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    cases i using Fin.cases with
    | zero => simpa only [singleSubsetDegreeWord, Fin.cases_zero] using w.property.2.symm
    | succ j =>
      have hrest := (singleExceptionalWord_at_anchor w.val 4 (by omega) w.property.2).mp
        w.property.1.2 j
      dsimp only
      simp only [singleSubsetDegreeWord, Fin.cases_succ, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · exact h.symm
      · rcases hrest with hz | ht
        · exact hz.symm
        · exact (h ht).elim
  right_inv s := by
    apply Subtype.ext
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    try dsimp only
    simp only [singleSubsetDegreeWord, Fin.cases_succ]
    split_ifs <;> simp_all

open scoped Classical in
theorem single_anchored_word_count (k : Nat) (hk : 1 ≤ k) :
    Fintype.card {w : CyclicDegreeWord (2 * k + 2) //
      ((∑ i, (w i).val = 2 * k + 2) ∧ SingleExceptionalWord w 4) ∧ (w 0).val = 4} =
      (2 * k + 2).choose (k - 1) := by
  classical
  rw [Fintype.card_congr (singleAnchoredWordEquiv k hk), Fintype.card_finset_len,
    Fintype.card_fin]

#print axioms single_anchored_word_count

end LC004

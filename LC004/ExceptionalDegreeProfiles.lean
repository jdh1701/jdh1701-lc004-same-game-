import LC004.NoncrossingDegreeWordEquiv

namespace LC004
open scoped BigOperators

def SingleExceptionalWord {n : Nat} (w : CyclicDegreeWord n) (a : Nat) : Prop :=
  ∃ i, (w i).val = a ∧ ∀ j, j ≠ i → (w j).val = 0 ∨ (w j).val = 2

def DoubleExceptionalWord {n : Nat} (w : CyclicDegreeWord n) (a : Nat) : Prop :=
  ∃ i j, i ≠ j ∧ (w i).val = a ∧ (w j).val = a ∧
    ∀ t, t ≠ i → t ≠ j → (w t).val = 0 ∨ (w t).val = 2

theorem singleExceptionalWord_rotate {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (r : Fin (n + 1)) :
    SingleExceptionalWord (rotateDegreeWord w r) a ↔ SingleExceptionalWord w a := by
  constructor
  · rintro ⟨i, hi, hrest⟩
    refine ⟨r + i, hi, ?_⟩
    intro j hj
    have hne : -r + j ≠ i := by
      intro h
      have h' := congrArg (fun t => r + t) h
      simp only [add_neg_cancel_left] at h'
      exact hj h'
    have h := hrest (-r + j) hne
    simpa only [rotateDegreeWord, add_neg_cancel_left] using h
  · rintro ⟨i, hi, hrest⟩
    refine ⟨-r + i, ?_, ?_⟩
    · simpa only [rotateDegreeWord, add_neg_cancel_left] using hi
    · intro j hj
      exact hrest (r + j) (by
        intro h
        apply hj
        simpa only [neg_add_cancel_left] using congrArg (fun t => -r + t) h)

theorem doubleExceptionalWord_rotate {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (r : Fin (n + 1)) :
    DoubleExceptionalWord (rotateDegreeWord w r) a ↔ DoubleExceptionalWord w a := by
  constructor
  · rintro ⟨i, j, hij, hi, hj, hrest⟩
    refine ⟨r + i, r + j, fun h => hij (add_left_cancel h), hi, hj, ?_⟩
    intro t hti htj
    have hne (s : Fin (n + 1)) (hs : t ≠ r + s) : -r + t ≠ s := by
      intro h
      apply hs
      simpa only [add_neg_cancel_left] using congrArg (fun u => r + u) h
    have h := hrest (-r + t) (hne i hti) (hne j htj)
    simpa only [rotateDegreeWord, add_neg_cancel_left] using h
  · rintro ⟨i, j, hij, hi, hj, hrest⟩
    refine ⟨-r + i, -r + j, fun h => hij (add_left_cancel h), ?_, ?_, ?_⟩
    · simpa only [rotateDegreeWord, add_neg_cancel_left] using hi
    · simpa only [rotateDegreeWord, add_neg_cancel_left] using hj
    · intro t hti htj
      have hne (s : Fin (n + 1)) (hs : t ≠ -r + s) : r + t ≠ s := by
        intro h
        apply hs
        simpa only [neg_add_cancel_left] using congrArg (fun u => -r + u) h
      exact hrest (r + t) (hne i hti) (hne j htj)

open scoped Classical in
theorem degreeWord_sum_rotate {n : Nat} (w : CyclicDegreeWord n) (r : Fin (n + 1)) :
    (∑ i, (rotateDegreeWord w r i).val) = ∑ i, (w i).val := by
  classical
  exact Fintype.sum_equiv (Equiv.addLeft r) _ _ (fun _ => rfl)

open scoped Classical in
theorem singleExceptionalWord_arity_card {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (ha : 2 < a) (hw : SingleExceptionalWord w a) :
    Fintype.card {i : Fin (n + 1) // (w i).val = a} = 1 := by
  classical
  obtain ⟨i, hi, hrest⟩ := hw
  have hfilter : (Finset.univ : Finset (Fin (n + 1))).filter (fun j => (w j).val = a) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      rcases hrest j hne with h | h <;> omega
    · intro h
      simpa only [h] using hi
  rw [Fintype.card_subtype, hfilter, Finset.card_singleton]

open scoped Classical in
theorem doubleExceptionalWord_arity_card {n : Nat} (w : CyclicDegreeWord n)
    (a : Nat) (ha : 2 < a) (hw : DoubleExceptionalWord w a) :
    Fintype.card {i : Fin (n + 1) // (w i).val = a} = 2 := by
  classical
  obtain ⟨i, j, hij, hi, hj, hrest⟩ := hw
  have hfilter : (Finset.univ : Finset (Fin (n + 1))).filter (fun t => (w t).val = a) = {i, j} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro ht
      by_contra hne
      push_neg at hne
      rcases hrest t hne.1 hne.2 with h | h <;> omega
    · rintro (rfl | rfl) <;> assumption
  rw [Fintype.card_subtype, hfilter, Finset.card_pair hij]

#print axioms singleExceptionalWord_arity_card
#print axioms doubleExceptionalWord_arity_card

end LC004

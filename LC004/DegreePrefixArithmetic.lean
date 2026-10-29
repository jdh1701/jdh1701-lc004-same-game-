import LC004.PartitionIntervalDegrees

namespace LC004
open scoped BigOperators

noncomputable def degreePrefix {n : Nat} (d : Fin n → Nat) (cut : Nat) : Nat := by
  classical
  exact ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i.val < cut), d i

open scoped Classical in
theorem degreePrefix_total {n : Nat} (d : Fin n → Nat) :
    degreePrefix d n = ∑ i, d i := by
  classical
  have hf : (Finset.univ : Finset (Fin n)).filter (fun i => i.val < n) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro i.isLt
  simp only [degreePrefix, hf]

theorem degreePrefix_castLE {m n : Nat} (d : Fin n → Nat) (hmn : m ≤ n)
    (cut : Nat) (hcut : cut ≤ m) :
    degreePrefix (fun i : Fin m => d (Fin.castLE hmn i)) cut = degreePrefix d cut := by
  classical
  unfold degreePrefix
  refine Finset.sum_bij (fun i _ => Fin.castLE hmn i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj heq
    exact Fin.ext (congrArg (fun t : Fin n => t.val) heq)
  · intro j hj
    have hval := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val, lt_of_lt_of_le hval hcut⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩, ?_⟩
    exact Fin.ext rfl
  · intro i hi
    rfl

def degreeTruncate {m n : Nat} (d : Fin n → Nat) (hmn : m ≤ n)
    (gap : Nat) (i : Fin m) : Nat :=
  if i.val < gap then d (Fin.castLE hmn i) else 0

theorem degreeTruncate_prefix {m n : Nat} (d : Fin n → Nat) (hmn : m ≤ n)
    (gap : Nat) (hgap : gap ≤ m) (cut : Nat) :
    degreePrefix (degreeTruncate d hmn gap) cut = degreePrefix d (min cut gap) := by
  classical
  unfold degreePrefix degreeTruncate
  rw [← Finset.sum_filter]
  have hf : ((Finset.univ : Finset (Fin m)).filter (fun i => i.val < cut)).filter
      (fun i => i.val < gap) = Finset.univ.filter (fun i => i.val < min cut gap) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_min_iff]
  rw [hf]
  exact degreePrefix_castLE d hmn (min cut gap) ((min_le_right cut gap).trans hgap)

open scoped Classical in
theorem degree_sum_last_support {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hsupport : ∀ j, i < j → d j = 0) :
    (∑ j, d j) = degreePrefix d i.val + d i := by
  classical
  have hsub : ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < i.val)) ⊆
      Finset.univ.erase i := by
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    exact Finset.mem_erase.mpr ⟨by intro h; subst j; omega, Finset.mem_univ _⟩
  have hs : degreePrefix d i.val = ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, d j := by
    apply Finset.sum_subset hsub
    intro j hj hn
    have hnot : ¬ j.val < i.val := by
      intro hlt
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have hne := (Finset.mem_erase.mp hj).1
    exact hsupport j (lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) d (Finset.mem_univ i)
  rw [← hs] at h
  exact h.symm

open scoped Classical in
theorem exists_last_positive_degree {n : Nat} (d : Fin n → Nat)
    (hpos : 0 < ∑ i, d i) :
    ∃ i, 0 < d i ∧ ∀ j, i < j → d j = 0 := by
  classical
  have he : ∃ i, 0 < d i := by
    by_contra h
    push_neg at h
    have hz : ∀ i, d i = 0 := fun i => Nat.eq_zero_of_le_zero (h i)
    simp only [hz, Finset.sum_const_zero] at hpos
    omega
  obtain ⟨j, hj⟩ := he
  let s := (Finset.univ : Finset (Fin n)).filter (fun i => 0 < d i)
  have hs : s.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let i := s.max' hs
  have hi := Finset.max'_mem s hs
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  intro t hit
  by_contra ht
  have htp : 0 < d t := Nat.pos_of_ne_zero ht
  have htmem : t ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htp⟩
  have hle := Finset.le_max' s t htmem
  exact (not_lt_of_ge hle) hit

end LC004

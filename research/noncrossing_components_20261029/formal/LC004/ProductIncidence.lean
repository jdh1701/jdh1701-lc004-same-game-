import LC004.FiniteIncidenceSupport

namespace LC004
open scoped BigOperators Classical

theorem lowerIncidence_eq_on_ideal {α : Type*} [Fintype α] [SemilatticeInf α]
    (f g : α → Int) (p : α)
    (h : ∀ r, r ≤ p → lowerIncidence f r = lowerIncidence g r) : f p = g p := by
  have he : lowerIncidence (fun q => if q ≤ p then f q else 0) =
      lowerIncidence (fun q => if q ≤ p then g q else 0) := by
    funext r
    rw [lowerIncidence_truncate,lowerIncidence_truncate]
    exact h _ inf_le_right
  have hv := congrFun (lowerIncidence_injective he) p
  simpa using hv

theorem lowerIncidence_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, PartialOrder (α i)]
    (c : ∀ i, α i → Int) (p : ∀ i, α i) :
    lowerIncidence (fun q : ∀ i, α i => ∏ i, c i (q i)) p =
      ∏ i, lowerIncidence (c i) (p i) := by
  classical
  unfold lowerIncidence
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : q ≤ p
  · simp only [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    simp [h i]
  · rw [if_neg h]
    have hn : ∃ i, ¬ q i ≤ p i := by
      by_contra he
      push_neg at he
      exact h he
    obtain ⟨i,hi⟩ := hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

#print axioms lowerIncidence_eq_on_ideal
#print axioms lowerIncidence_pi_product

theorem lowerIncidence_orderIso {α β : Type*} [Fintype α] [Fintype β]
    [PartialOrder α] [PartialOrder β] (e : α ≃o β) (f : β → Int) (p : α) :
    lowerIncidence (fun q => f (e q)) p = lowerIncidence f (e p) := by
  classical
  unfold lowerIncidence
  apply Fintype.sum_equiv e.toEquiv
  intro q
  change (if q ≤ p then f (e q) else 0) = if e q ≤ e p then f (e q) else 0
  simp only [e.le_iff_le]

theorem lowerIncidence_Iic {α : Type*} [Fintype α] [PartialOrder α]
    (f : α → Int) (pi : α) (p : {q : α // q ≤ pi}) :
    lowerIncidence (fun q : {q : α // q ≤ pi} => f q.val) p = lowerIncidence f p.val := by
  classical
  unfold lowerIncidence
  symm
  apply Finset.sum_congr_set {q : α | q ≤ pi}
    (fun q => if q ≤ p.val then f q else 0)
    (fun q => if q ≤ p then f q.val else 0)
  · intro q _
    rfl
  · intro q hq
    have hn : ¬ q ≤ p.val := fun h => hq (le_trans h p.property)
    simp [hn]

#print axioms lowerIncidence_orderIso
#print axioms lowerIncidence_Iic
end LC004

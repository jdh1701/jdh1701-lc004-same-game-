import LC004.MatchingPartner
import Mathlib.Combinatorics.Enumerative.DyckWord

namespace LC004
open scoped BigOperators

theorem list_count_eq_sum_indicator {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    l.count a = (l.map (fun x => if x = a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = a <;> simp [List.count_cons, hx, ih, Nat.add_comm]

/-- Convert prefix counts in an indexed word to finite position counts. -/
theorem count_take_ofFn_eq_card {α : Type*} [DecidableEq α] {n : Nat}
    (f : Fin n → α) (a : α) (k : Nat) :
    ((List.ofFn f).take k).count a =
      ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < k ∧ f i = a)).card := by
  rw [list_count_eq_sum_indicator, List.map_take, List.map_ofFn, List.sum_take_ofFn]
  simp only [Function.comp_apply, Finset.sum_boole, Finset.filter_filter, Nat.cast_id]

noncomputable def matchingDyckStep {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) : DyckStep := by
  classical
  exact if i < matchingPartner p hp i then DyckStep.U else DyckStep.D

theorem matchingDyckStep_U_iff {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) :
    matchingDyckStep p hp i = DyckStep.U ↔ i < matchingPartner p hp i := by
  classical
  simp [matchingDyckStep]

theorem matchingDyckStep_D_iff {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) :
    matchingDyckStep p hp i = DyckStep.D ↔ matchingPartner p hp i < i := by
  classical
  by_cases hi : i < matchingPartner p hp i
  · have hn : ¬ matchingPartner p hp i < i := not_lt_of_ge (le_of_lt hi)
    simp [matchingDyckStep, hi, hn]
  · have hn := (matchingPartner_spec p hp i).1
    have hc : matchingPartner p hp i < i := by omega
    simp [matchingDyckStep, hi, hc]

theorem matching_prefix_U_count {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (k : Nat) :
    ((List.ofFn (matchingDyckStep p hp)).take k).count DyckStep.U =
      (matchingOpensBefore p hp k).card := by
  classical
  rw [count_take_ofFn_eq_card]
  apply congrArg Finset.card
  ext i
  simp only [matchingOpensBefore, Finset.mem_filter, Finset.mem_univ,
    true_and, matchingDyckStep_U_iff]

theorem matching_prefix_D_count {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (k : Nat) :
    ((List.ofFn (matchingDyckStep p hp)).take k).count DyckStep.D =
      (matchingClosesBefore p hp k).card := by
  classical
  rw [count_take_ofFn_eq_card]
  apply congrArg Finset.card
  ext i
  simp only [matchingClosesBefore, Finset.mem_filter, Finset.mem_univ,
    true_and, matchingDyckStep_D_iff]

/-- Forward construction toward the Catalan bijection. This is a map
into genuine mathlib Dyck words; injectivity and surjectivity are not
asserted by this construction. -/
noncomputable def matchingToDyckWord {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) : DyckWord where
  toList := List.ofFn (matchingDyckStep p hp)
  count_U_eq_count_D := by
    have hu := matching_prefix_U_count p hp n
    have hd := matching_prefix_D_count p hp n
    have ht : (List.ofFn (matchingDyckStep p hp)).take n =
        List.ofFn (matchingDyckStep p hp) := List.take_of_length_le (by simp)
    rw [ht] at hu hd
    exact hu.trans ((matching_opens_closes_card p hp).trans hd.symm)
  count_D_le_count_U := by
    intro k
    rw [matching_prefix_D_count, matching_prefix_U_count]
    exact matching_closes_before_le_opens p hp k

theorem matchingToDyckWord_length {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) : (matchingToDyckWord p hp).toList.length = n := by
  simp [matchingToDyckWord]

theorem matchingToDyckWord_semilength (m : Nat) (p : ColorPattern (2 * m))
    (hp : NoncrossingPairPattern p) : (matchingToDyckWord p hp).semilength = m := by
  have h := (matchingToDyckWord p hp).two_mul_semilength_eq_length
  rw [matchingToDyckWord_length] at h
  omega

noncomputable def matchingDyckMap (m : Nat) :
    {p : ColorPattern (2 * m) // NoncrossingPairPattern p} →
      {w : DyckWord // w.semilength = m} :=
  fun p => ⟨matchingToDyckWord p.val p.property,
    matchingToDyckWord_semilength m p.val p.property⟩

#print axioms count_take_ofFn_eq_card
#print axioms matchingToDyckWord
#print axioms matchingToDyckWord_semilength

end LC004

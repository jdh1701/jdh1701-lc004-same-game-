import LC004.MatchingRepresentationCardinality

namespace LC004

noncomputable def matchingPartner {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) : Fin n :=
  Classical.choose (pair_pattern_has_other p hp i)

theorem matchingPartner_spec {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) :
    matchingPartner p hp i ≠ i ∧ p i (matchingPartner p hp i) :=
  Classical.choose_spec (pair_pattern_has_other p hp i)

theorem matchingPartner_unique {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i j : Fin n) (hne : j ≠ i) (hrel : p i j) :
    matchingPartner p hp i = j := by
  have hs := matchingPartner_spec p hp i
  rcases (pair_pattern_rel_iff p hp hs.1.symm hs.2 j).mp hrel with h | h
  · exact (hne h).elim
  · exact h.symm

theorem matchingPartner_twice {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (i : Fin n) :
    matchingPartner p hp (matchingPartner p hp i) = i := by
  have hs := matchingPartner_spec p hp i
  exact matchingPartner_unique p hp (matchingPartner p hp i) i hs.1.symm (p.symm hs.2)

theorem matchingPartner_injective {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) : Function.Injective (matchingPartner p hp) := by
  intro i j h
  have hh := congrArg (matchingPartner p hp) h
  simpa only [matchingPartner_twice] using hh

noncomputable def matchingOpensBefore {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (k : Nat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => i.val < k ∧ i < matchingPartner p hp i)

noncomputable def matchingClosesBefore {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (k : Nat) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => i.val < k ∧ matchingPartner p hp i < i)

/-- Each closing endpoint in a prefix maps injectively to its opening
endpoint in the same prefix. This proves the Dyck prefix inequality. -/
theorem matching_closes_before_le_opens {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) (k : Nat) :
    (matchingClosesBefore p hp k).card ≤ (matchingOpensBefore p hp k).card := by
  classical
  apply Finset.card_le_card_of_injOn (matchingPartner p hp)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change (matchingPartner p hp i).val < k
      have hc : (matchingPartner p hp i).val < i.val := h.2
      omega
    · rw [matchingPartner_twice]
      exact h.2
  · intro i _ j _ h
    exact matchingPartner_injective p hp h

theorem matching_opens_closes_card {n : Nat} (p : ColorPattern n)
    (hp : NoncrossingPairPattern p) :
    (matchingOpensBefore p hp n).card = (matchingClosesBefore p hp n).card := by
  classical
  apply Nat.le_antisymm _ (matching_closes_before_le_opens p hp n)
  apply Finset.card_le_card_of_injOn (matchingPartner p hp)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (matchingPartner p hp i).isLt, ?_⟩
    rw [matchingPartner_twice]
    exact h.2
  · intro i _ j _ h
    exact matchingPartner_injective p hp h

#print axioms matchingPartner_twice
#print axioms matching_closes_before_le_opens
#print axioms matching_opens_closes_card

end LC004

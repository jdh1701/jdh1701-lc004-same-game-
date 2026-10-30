import LC004.FiveCoordinateGeometry

namespace LC004
open scoped Classical

/-- Relabeling by a bijection preserves the full equivalence-relation lattice. -/
def setoidComapOrderIso {α β : Type*} (e : α ≃ β) : Setoid β ≃o Setoid α where
  toFun := Setoid.comap e
  invFun := Setoid.comap e.symm
  left_inv := setoid_comap_equiv_cancel e.symm
  right_inv := setoid_comap_equiv_cancel e
  map_rel_iff' := setoid_comap_equiv_le_iff e _ _

theorem fiveEncodedPattern_join_iff {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (a b : Fin (Fintype.card (Quotient p)) → Fin 10) :
    fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p ↔
      fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b =
        fiveClassBaseSetoid (Fintype.card (Quotient p)) := by
  have hs := (setoidComapOrderIso (fivePatternCoordinates p hfive)).map_sup
    (fiveAssignmentSetoid a) (fiveAssignmentSetoid b)
  change Setoid.comap (fivePatternCoordinates p hfive) (_ ⊔ _) =
    fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b at hs
  constructor
  · intro h
    apply setoid_comap_equiv_injective (fivePatternCoordinates p hfive)
    exact hs.trans (h.trans (fivePatternCoordinates_base p hfive))
  · intro h
    calc
      _ = Setoid.comap (fivePatternCoordinates p hfive)
          (fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b) := hs.symm
      _ = Setoid.comap (fivePatternCoordinates p hfive)
          (fiveClassBaseSetoid _) := congrArg _ h
      _ = p := (fivePatternCoordinates_base p hfive).symm

/-- All geometric and incidence bridges are discharged: this is the original
collected coefficient, not merely a class/rank model's alternating sum. -/
theorem winningJoinCoefficient_five_encoded_law {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    [Nontrivial (Fin (Fintype.card (Quotient p)))]
    (hconn : FiveClassCrossingConnected
      (fiveCoordinateClassPositions (fivePatternCoordinates p hfive))) :
    winningJoinCoefficient n p =
      if (∃ a b, fiveEncodedNCTuples p hfive = {a,b} ∧
        fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p) then -1 else 0 := by
  classical
  rw [winningJoinCoefficient_five_eq_choice_sum, fiveEncodedNCTuples_eq_splitFamily]
  have h := fiveClassSplitFamily_join_survival_law
    (fiveCoordinateClassPositions (fivePatternCoordinates p hfive))
    (fiveCoordinateClassPositions_card _)
    (fiveCoordinateClassPositions_disjoint _) hconn
  simpa only [fiveEncodedPattern_join_iff] using h

/-- The two-survivor criterion stated solely with original CertificateConstraint
patterns and their join. The crossing condition concerns the original classes'
positions; at least two classes is essential. -/
theorem winningJoinCoefficient_five_original_law {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    [Nontrivial (Fin (Fintype.card (Quotient p)))]
    (hconn : FiveClassCrossingConnected
      (fiveCoordinateClassPositions (fivePatternCoordinates p hfive))) :
    winningJoinCoefficient n p =
      if (∃ c d : ColorPattern n,
        Finset.univ.filter (fun r => CertificateConstraint r ∧ r ≤ p) = {c,d} ∧
        c ⊔ d = p) then -1 else 0 := by
  classical
  have he : (∃ a b, fiveEncodedNCTuples p hfive = {a,b} ∧
      fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p) ↔
      (∃ c d : ColorPattern n,
        Finset.univ.filter (fun r => CertificateConstraint r ∧ r ≤ p) = {c,d} ∧
        c ⊔ d = p) := by
    constructor
    · rintro ⟨a,b,hab,hjoin⟩
      refine ⟨fiveEncodedPattern p hfive a,fiveEncodedPattern p hfive b,?_,hjoin⟩
      rw [five_certificate_generators_image,hab]
      simp only [Finset.image_insert,Finset.image_singleton]
    · rintro ⟨c,d,hcd,hjoin⟩
      have hc : c ∈ (fiveEncodedNCTuples p hfive).image (fiveEncodedPattern p hfive) := by
        rw [← five_certificate_generators_image,hcd]
        exact Finset.mem_insert_self _ _
      have hd : d ∈ (fiveEncodedNCTuples p hfive).image (fiveEncodedPattern p hfive) := by
        rw [← five_certificate_generators_image,hcd]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hd
      refine ⟨a,b,?_,hjoin⟩
      apply Finset.image_injective (fiveEncodedPattern_injective p hfive)
      rw [← five_certificate_generators_image,hcd]
      simp only [Finset.image_insert,Finset.image_singleton]
  have h := winningJoinCoefficient_five_encoded_law p hfive hconn
  by_cases hs : ∃ a b, fiveEncodedNCTuples p hfive = {a,b} ∧
      fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p
  · rw [if_pos hs] at h
    rw [if_pos (he.mp hs)]
    exact h
  · rw [if_neg hs] at h
    rw [if_neg (fun hc => hs (he.mpr hc))]
    exact h

/-- The original coefficient can be recognized from a valid separated pair
and its raw local implication graph, without enumerating the full family. -/
theorem winningJoinCoefficient_five_scc_law {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    [Nontrivial (Fin (Fintype.card (Quotient p)))]
    (hconn : FiveClassCrossingConnected
      (fiveCoordinateClassPositions (fivePatternCoordinates p hfive))) :
    winningJoinCoefficient n p =
      if (∃ a b, a ∈ fiveEncodedNCTuples p hfive ∧ b ∈ fiveEncodedNCTuples p hfive ∧
        (∀ i, a i ≠ b i) ∧
        ChoiceImplicationStrong (fun i j => FiveActualCompatible
          (fiveCoordinateClassPositions (fivePatternCoordinates p hfive) i)
          (fiveCoordinateClassPositions (fivePatternCoordinates p hfive) j)) a b)
      then -1 else 0 := by
  classical
  let G := fiveCoordinateClassPositions (fivePatternCoordinates p hfive)
  have hA := fiveEncodedNCTuples_eq_splitFamily p hfive
  have he : (∃ a b, fiveEncodedNCTuples p hfive = {a,b} ∧
      fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p) ↔
      (∃ a b, a ∈ fiveEncodedNCTuples p hfive ∧ b ∈ fiveEncodedNCTuples p hfive ∧
        (∀ i, a i ≠ b i) ∧
        ChoiceImplicationStrong (fun i j => FiveActualCompatible (G i) (G j)) a b) := by
    constructor
    · rintro ⟨a,b,hab,hjoin⟩
      have ha : a ∈ fiveEncodedNCTuples p hfive := hab.symm ▸ Finset.mem_insert_self a {b}
      have hb : b ∈ fiveEncodedNCTuples p hfive := hab.symm ▸
        Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have hsep := (fiveAssignmentSetoid_join_eq_base_iff a b).mp
        ((fiveEncodedPattern_join_iff p hfive a b).mp hjoin)
      refine ⟨a,b,ha,hb,hsep,?_⟩
      exact (fiveClass_survivor_pair_iff_strong G (fiveCoordinateClassPositions_card _)
        (fiveCoordinateClassPositions_disjoint _) hconn a b (hA ▸ ha) (hA ▸ hb) hsep).mp
          (hA.symm.trans hab)
    · rintro ⟨a,b,ha,hb,hsep,hstrong⟩
      refine ⟨a,b,?_,(fiveEncodedPattern_join_iff p hfive a b).mpr
        ((fiveAssignmentSetoid_join_eq_base_iff a b).mpr hsep)⟩
      exact hA.trans ((fiveClass_survivor_pair_iff_strong G (fiveCoordinateClassPositions_card _)
        (fiveCoordinateClassPositions_disjoint _) hconn a b (hA ▸ ha) (hA ▸ hb) hsep).mpr hstrong)
  have h := winningJoinCoefficient_five_encoded_law p hfive hconn
  by_cases hs : ∃ a b, fiveEncodedNCTuples p hfive = {a,b} ∧
      fiveEncodedPattern p hfive a ⊔ fiveEncodedPattern p hfive b = p
  · rw [if_pos hs] at h
    rw [if_pos (he.mp hs)]
    exact h
  · rw [if_neg hs] at h
    rw [if_neg (fun hc => hs (he.mpr hc))]
    exact h

/-- The connected all-five coefficient has no other possible integer values. -/
theorem winningJoinCoefficient_five_range {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    [Nontrivial (Fin (Fintype.card (Quotient p)))]
    (hconn : FiveClassCrossingConnected
      (fiveCoordinateClassPositions (fivePatternCoordinates p hfive))) :
    winningJoinCoefficient n p = -1 ∨ winningJoinCoefficient n p = 0 := by
  rw [winningJoinCoefficient_five_original_law p hfive hconn]
  split_ifs <;> simp

/-- Cancellation stated directly in terms of the number of ORIGINAL certificate
partitions, without an assumed encoding or face-sum identity. -/
theorem winningJoinCoefficient_five_zero_of_three_generators {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    [Nontrivial (Fin (Fintype.card (Quotient p)))]
    (hconn : FiveClassCrossingConnected
      (fiveCoordinateClassPositions (fivePatternCoordinates p hfive)))
    (hthree : 3 ≤ (Finset.univ.filter
      (fun c : ColorPattern n => CertificateConstraint c ∧ c ≤ p)).card) :
    winningJoinCoefficient n p = 0 := by
  classical
  rw [winningJoinCoefficient_five_original_law p hfive hconn]
  apply if_neg
  rintro ⟨c,d,hcd,_⟩
  rw [hcd] at hthree
  have hcard : ({c,d} : Finset (ColorPattern n)).card ≤ 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le c ({d} : Finset (ColorPattern n))
  omega

#print axioms winningJoinCoefficient_five_range
#print axioms winningJoinCoefficient_five_zero_of_three_generators
#print axioms winningJoinCoefficient_five_scc_law
#print axioms winningJoinCoefficient_five_original_law
end LC004

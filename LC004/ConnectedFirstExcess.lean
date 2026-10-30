import LC004.ConnectedCoefficientSupport

namespace LC004
open scoped BigOperators Classical

/-- A finite family of natural numbers summing to one has exactly one unit. -/
theorem fintype_nat_sum_one_shape {α : Type*} [Fintype α] (f : α → Nat)
    (h : ∑ a, f a = 1) : ∃ a, f a = 1 ∧ ∀ b, b ≠ a → f b = 0 := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : ∑ a, f a = 0 := Finset.sum_eq_zero (fun a _ => hn a)
    omega
  have hle : f a ≤ ∑ b, f b :=
    Finset.single_le_sum (fun b _ => Nat.zero_le (f b)) (Finset.mem_univ a)
  have ha1 : f a = 1 := by omega
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have hz : ∑ b ∈ Finset.univ.erase a, f b = 0 := by omega
  refine ⟨a,ha1,?_⟩
  intro b hba
  have hb : f b ≤ ∑ c ∈ Finset.univ.erase a, f c :=
    Finset.single_le_sum (fun c _ => Nat.zero_le (f c))
      (Finset.mem_erase.mpr ⟨hba,Finset.mem_univ b⟩)
  omega

/-- The entire size excess is the sum of the individual class excesses. -/
theorem ncConnected_nonzero_excess_sum {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hk : 2 ≤ Nat.card (Quotient p))
    (hne : winningJoinCoefficient n p ≠ 0) :
    (∑ q : Quotient p, ((patternQuotientFiber p q).card - 5)) =
      n - 5 * Nat.card (Quotient p) := by
  classical
  have hs := ncConnected_nonzero_every_class_min_five p hc
    (pattern_not_top_of_two_classes p hk) hne
  have hlow (q : Quotient p) : 5 ≤ (patternQuotientFiber p q).card := by
    rw [patternQuotientFiber_eq_class]
    exact hs q.out
  have he : (∑ q : Quotient p, ((patternQuotientFiber p q).card - 5 + 5)) = n := by
    calc
      _ = ∑ q : Quotient p, (patternQuotientFiber p q).card :=
        Finset.sum_congr rfl (fun q _ => Nat.sub_add_cancel (hlow q))
      _ = n := (pattern_card_sum_class_sizes p).symm
  have hadd : (∑ q : Quotient p, ((patternQuotientFiber p q).card - 5)) +
      5 * Nat.card (Quotient p) = n := by
    simpa [Finset.sum_add_distrib,Nat.card_eq_fintype_card,Nat.mul_comm] using he
  omega

/-- Exactly one six-point class and all remaining classes have size five. -/
def FirstExcessProfile {n : Nat} (p : ColorPattern n) : Prop :=
  ∃ q : Quotient p, (patternQuotientFiber p q).card = 6 ∧
    ∀ r : Quotient p, r ≠ q → (patternQuotientFiber p r).card = 5

/-- Uniform first-excess support: no other mixed profile can contribute. -/
theorem ncConnected_nonzero_first_excess {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hk : 2 ≤ Nat.card (Quotient p))
    (hne : winningJoinCoefficient n p ≠ 0)
    (hsize : n = 5 * Nat.card (Quotient p) + 1) : FirstExcessProfile p := by
  have hs := ncConnected_nonzero_every_class_min_five p hc
    (pattern_not_top_of_two_classes p hk) hne
  have hlow (q : Quotient p) : 5 ≤ (patternQuotientFiber p q).card := by
    rw [patternQuotientFiber_eq_class]
    exact hs q.out
  have he : (∑ q : Quotient p, ((patternQuotientFiber p q).card - 5)) = 1 := by
    rw [ncConnected_nonzero_excess_sum p hc hk hne]
    omega
  obtain ⟨q,hq,hr⟩ := fintype_nat_sum_one_shape _ he
  refine ⟨q,by have := hlow q; omega,?_⟩
  intro r hne
  have := hr r hne
  have := hlow r
  omega

/-- Restrict the actual connected coefficient to the first-excess profile.
This is a support identity, not an assumed formula for survivor counts. -/
theorem connectedClassCoefficient_first_excess (j : Nat) (hj : 2 ≤ j) :
    connectedClassCoefficient (5*j+1) j =
      ∑ p : {p : ColorPattern (5*j+1) // NCConnected p},
        if Nat.card (Quotient p.val) = j ∧ FirstExcessProfile p.val
        then winningJoinCoefficient (5*j+1) p.val else 0 := by
  classical
  unfold connectedClassCoefficient
  apply Finset.sum_congr rfl
  intro p _
  by_cases hk : Nat.card (Quotient p.val) = j
  · by_cases hz : winningJoinCoefficient (5*j+1) p.val = 0
    · simp [hk,hz]
    · have hp := ncConnected_nonzero_first_excess p.val p.property (by omega) hz (by omega)
      simp [hk,hp]
  · simp [hk]

#print axioms ncConnected_nonzero_excess_sum
#print axioms ncConnected_nonzero_first_excess
#print axioms connectedClassCoefficient_first_excess
end LC004

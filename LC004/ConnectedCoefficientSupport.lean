import LC004.ConnectedClassCrossing
import LC004.CrossedClassMinSize
import LC004.LocalGeneratorTransfer
import LC004.WeightedConnectedFibers

namespace LC004
open scoped BigOperators Classical

/-- Nonzero original coefficient supplies the least-upper-bound property of
the complete original certificate family, without an assumed join witness. -/
theorem winningJoinCoefficient_nonzero_minimal {n : Nat} (p : ColorPattern n)
    (hne : winningJoinCoefficient n p ≠ 0) (q : ColorPattern n)
    (hq : ∀ c, CertificateConstraint c → c ≤ p → c ≤ q) : p ≤ q := by
  by_contra h
  exact hne (winningJoinCoefficient_zero_of_common_refinement p q h hq)

/-- Extend the crossed-class bound to either orientation of either class,
and discharge the certificate-join hypotheses from the original coefficient. -/
theorem winningJoinCoefficient_nonzero_crossed_min_five {n : Nat}
    (p : ColorPattern n) (a : Fin n) (hne : winningJoinCoefficient n p ≠ 0)
    (hcross : PatternClassCrossed p a) : 5 ≤ (patternClassPositions p a).card := by
  classical
  obtain ⟨u,v,x,y,hau,hav,hxy,hax,hord⟩ := hcross
  let F := Finset.univ.filter (fun c : ColorPattern n => CertificateConstraint c ∧ c ≤ p)
  have hF : ∀ c ∈ F, CertificateConstraint c := fun c hc => (Finset.mem_filter.mp hc).2.1
  have hle : ∀ c ∈ F, c ≤ p := fun c hc => (Finset.mem_filter.mp hc).2.2
  have hmin : ∀ q : ColorPattern n, (∀ c ∈ F, c ≤ q) → p ≤ q := by
    intro q hq
    exact winningJoinCoefficient_nonzero_minimal p hne q
      (fun c hc hcp => hq c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,hcp⟩))
  have huv : p u v := p.trans (p.symm hau) hav
  have hux : ¬ p u x := fun h => hax (p.trans hau h)
  have huy : ¬ p u y := fun h => hax (p.trans (p.trans hau h) (p.symm hxy))
  have h4 : 4 ≤ (patternClassPositions p a).card := by
    by_contra h
    have hsmall : (patternClassPositions p u).card ≤ 3 := by
      rw [← patternClassPositions_eq_of_related p hau]
      omega
    rcases hord with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · exact join_small_class_no_cross hF hle hmin (h1.trans h2) huv hsmall
        hxy h1 h2 (by omega) huy
    · exact join_small_class_no_cross hF hle hmin (h2.trans h3) huv hsmall
        (p.symm hxy) h2 h3 (by omega) hux
  by_contra h5
  have hcard : (patternClassPositions p a).card = 4 := by omega
  let S := patternClassPositions p a
  let e := S.orderEmbOfFin hcard
  have hmem (i : Fin 4) : p a (e i) :=
    (mem_patternClassPositions_iff p a _).mp (S.orderEmbOfFin_mem hcard i)
  have hS : S = ({e 0,e 1,e 2,e 3} : Finset (Fin n)) := by
    ext z
    constructor
    · intro hz
      have hr : z ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hz
      obtain ⟨i,rfl⟩ := hr
      fin_cases i <;> simp
    · intro hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      all_goals exact S.orderEmbOfFin_mem hcard _
  have hS0 : patternClassPositions p (e 0) = {e 0,e 1,e 2,e 3} := by
    rw [← patternClassPositions_eq_of_related p (hmem 0)]
    exact hS
  exact hne (winningJoinCoefficient_crossed_four_zero p
    (e.strictMono (by decide : (0 : Fin 4) < 1))
    (e.strictMono (by decide : (1 : Fin 4) < 2))
    (e.strictMono (by decide : (2 : Fin 4) < 3)) hS0
    (p.trans (p.symm (hmem 0)) hau) (p.trans (p.symm (hmem 0)) hav)
    hxy (fun h => hax (p.trans (hmem 0) h)) hord)

/-- Every class of a nontrivial connected original contribution has size >= 5.
This is uniform over all sizes and all mixed profiles. -/
theorem ncConnected_nonzero_every_class_min_five {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hntop : p ≠ ⊤) (hne : winningJoinCoefficient n p ≠ 0) :
    ∀ a, 5 ≤ (patternClassPositions p a).card :=
  fun a => winningJoinCoefficient_nonzero_crossed_min_five p a hne
    (ncConnected_every_class_crossed p hc hntop a)

theorem pattern_card_sum_class_sizes {n : Nat} (p : ColorPattern n) :
    n = ∑ q : Quotient p, (patternQuotientFiber p q).card := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk p))
  simpa only [Fintype.card_sigma,Fintype.card_subtype,Fintype.card_fin,
    patternQuotientFiber] using h.symm

theorem pattern_not_top_of_two_classes {n : Nat} (p : ColorPattern n)
    (hk : 2 ≤ Nat.card (Quotient p)) : p ≠ ⊤ := by
  intro he
  subst p
  have h : Nat.card (Quotient (⊤ : ColorPattern n)) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (Quotient (⊤ : ColorPattern n)) ≤ Fintype.card Unit :=
        Fintype.card_le_of_injective (fun _ => ())
          (fun x y _ => Quotient.inductionOn₂ x y (fun _ _ => Quotient.sound trivial))
      _ = 1 := by simp
  omega

/-- The original nonzero connected support obeys the 5j threshold. -/
theorem ncConnected_nonzero_size_bound {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hk : 2 ≤ Nat.card (Quotient p))
    (hne : winningJoinCoefficient n p ≠ 0) : 5 * Nat.card (Quotient p) ≤ n := by
  have hs := ncConnected_nonzero_every_class_min_five p hc
    (pattern_not_top_of_two_classes p hk) hne
  calc
    5 * Nat.card (Quotient p) = 5 * Fintype.card (Quotient p) := by rw [Nat.card_eq_fintype_card]
    5 * Fintype.card (Quotient p) = ∑ _q : Quotient p, 5 := by simp [Nat.mul_comm]
    _ ≤ ∑ q : Quotient p, (patternQuotientFiber p q).card := Finset.sum_le_sum (fun q _ => by
      rw [patternQuotientFiber_eq_class]
      exact hs q.out)
    _ = n := (pattern_card_sum_class_sizes p).symm

theorem ncConnected_coefficient_zero_below_five_classes {n : Nat}
    (p : ColorPattern n) (hc : NCConnected p)
    (hk : 2 ≤ Nat.card (Quotient p)) (hsize : n < 5 * Nat.card (Quotient p)) :
    winningJoinCoefficient n p = 0 := by
  by_contra h
  exact (not_le_of_gt hsize) (ncConnected_nonzero_size_bound p hc hk h)

/-- Equality in the support threshold forces precisely the all-five profile. -/
theorem ncConnected_nonzero_threshold_all_five {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hk : 2 ≤ Nat.card (Quotient p))
    (hne : winningJoinCoefficient n p ≠ 0) (heq : n = 5 * Nat.card (Quotient p)) :
    ∀ a, (patternClassPositions p a).card = 5 := by
  have hs := ncConnected_nonzero_every_class_min_five p hc
    (pattern_not_top_of_two_classes p hk) hne
  have hle : ∀ q ∈ (Finset.univ : Finset (Quotient p)),
      5 ≤ (patternQuotientFiber p q).card := by
    intro q _
    rw [patternQuotientFiber_eq_class]
    exact hs q.out
  have he : (∑ _q : Quotient p, 5) = ∑ q : Quotient p, (patternQuotientFiber p q).card := by
    calc
      (∑ _q : Quotient p, 5) = 5 * Nat.card (Quotient p) := by
        simp [Nat.card_eq_fintype_card,Nat.mul_comm]
      _ = n := heq.symm
      _ = _ := pattern_card_sum_class_sizes p
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp he
  intro a
  have ha := (hall (Quotient.mk p a) (Finset.mem_univ _)).symm
  rw [patternQuotientFiber_eq_class] at ha
  have hrel : p (Quotient.mk p a).out a := Quotient.exact (Quotient.out_eq _)
  rwa [patternClassPositions_eq_of_related p hrel] at ha

/-- The coefficient of the alphabet-size monomial b^j in the connected weight. -/
noncomputable def connectedClassCoefficient (n j : Nat) : Int :=
  ∑ p : {p : ColorPattern n // NCConnected p},
    if Nat.card (Quotient p.val) = j then winningJoinCoefficient n p.val else 0

/-- The previously conjectured connected coefficient vanishing range. -/
theorem connectedClassCoefficient_zero_below_five_mul (n j : Nat)
    (hj : 2 ≤ j) (hsize : n < 5 * j) : connectedClassCoefficient n j = 0 := by
  classical
  unfold connectedClassCoefficient
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with h
  · apply ncConnected_coefficient_zero_below_five_classes p.val p.property
    · omega
    · omega
  · rfl

noncomputable def connectedGamePolynomial (n : Nat) : Polynomial Int :=
  ∑ p : {p : ColorPattern n // NCConnected p},
    Polynomial.C (winningJoinCoefficient n p.val) * Polynomial.X ^ Nat.card (Quotient p.val)

theorem connectedGamePolynomial_coeff (n j : Nat) :
    (connectedGamePolynomial n).coeff j = connectedClassCoefficient n j := by
  classical
  simp [connectedGamePolynomial,connectedClassCoefficient,Polynomial.coeff_C_mul,eq_comm]

/-- This is the actual connected weight in the original-game moment formula,
not a newly postulated sequence. -/
theorem connectedGamePolynomial_eval (n : Nat) (b : Int) :
    (connectedGamePolynomial n).eval b = connectedGameWeight b n := by
  simp [connectedGamePolynomial,connectedGameWeight,weightedGameCoefficient,
    Polynomial.eval_finset_sum]

theorem connectedGamePolynomial_coeff_zero (n j : Nat)
    (hj : 2 ≤ j) (hsize : n < 5 * j) : (connectedGamePolynomial n).coeff j = 0 := by
  rw [connectedGamePolynomial_coeff]
  exact connectedClassCoefficient_zero_below_five_mul n j hj hsize

/-- All nonlinear alphabet-degree terms obey the uniform 5j support threshold. -/
theorem connectedGamePolynomial_natDegree_le (n : Nat) :
    (connectedGamePolynomial n).natDegree ≤ max 1 (n / 5) := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  exact connectedGamePolynomial_coeff_zero n j (by omega) (by omega)

#print axioms ncConnected_nonzero_every_class_min_five
#print axioms ncConnected_nonzero_size_bound
#print axioms connectedClassCoefficient_zero_below_five_mul
#print axioms connectedGamePolynomial_eval
#print axioms connectedGamePolynomial_natDegree_le
#print axioms ncConnected_nonzero_threshold_all_five
end LC004

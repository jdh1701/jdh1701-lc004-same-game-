import LC004.ConnectedCoefficientSupport

namespace LC004

/-- A small class of a nonzero refinement cannot cross any other class. -/
theorem nonzero_small_refinement_not_crossed {n : Nat} (q : ColorPattern n)
    (u : Fin n) (hne : winningJoinCoefficient n q ≠ 0)
    (hsmall : (patternClassPositions q u).card ≤ 4) :
    ¬ PatternClassCrossed q u := by
  intro hcross
  have h := winningJoinCoefficient_nonzero_crossed_min_five q u hne hcross
  omega

/-- Splitting one original class, while preserving every outside class, cannot
leave a nonempty gap between consecutive original occurrences identified by a
small class of the refinement, if the refinement coefficient is nonzero. -/
theorem ncConnected_small_refinement_gap_empty {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, u < x → x < v → ¬ p u x)
    (hne : winningJoinCoefficient n q ≠ 0)
    (hsmall : (patternClassPositions q u).card ≤ 4) :
    ∀ x, ¬ (u < x ∧ x < v) := by
  have hn := nonzero_small_refinement_not_crossed q u hne hsmall
  have hsat : ∀ x y, p x y → (u < x ∧ x < v) → (u < y ∧ y < v) := by
    intro x y hxy hx
    have hpx : ¬ p u x := hgap x hx.1 hx.2
    have hpy : ¬ p u y := fun h => hpx (p.trans h (p.symm hxy))
    have hqxy : q x y := houtside x y hpx hxy
    have hneU : y ≠ u := by intro h; subst y; exact hpy (p.refl u)
    have hneV : y ≠ v := by intro h; subst y; exact hpy (hle hquv)
    by_cases hyu : y < u
    · exact (hn ⟨u,v,y,x,q.refl u,hquv,q.symm hqxy,
        fun h => hpy (hle h),Or.inr ⟨hyu,hx.1,hx.2⟩⟩).elim
    · by_cases hvy : v < y
      · exact (hn ⟨u,v,x,y,q.refl u,hquv,hqxy,
          fun h => hpx (hle h),Or.inl ⟨hx.1,hx.2,hvy⟩⟩).elim
      · constructor <;> omega
  intro x hx
  exact ncConnected_no_saturated_interval p hc (fun z => u < z ∧ z < v)
    (by intros; omega) hsat x u hx (by omega)

theorem ncConnected_small_refinement_gap_adjacent {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (huv : u < v) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, u < x → x < v → ¬ p u x)
    (hne : winningJoinCoefficient n q ≠ 0)
    (hsmall : (patternClassPositions q u).card ≤ 4) : v.val = u.val + 1 := by
  have he := ncConnected_small_refinement_gap_empty p q hc hle u v hquv
    houtside hgap hne hsmall
  by_contra h
  let x : Fin n := ⟨u.val + 1, by omega⟩
  exact he x (by change u.val < u.val + 1 ∧ u.val + 1 < v.val; omega)

/-- The complementary circular gap is handled directly, without assuming
rotation invariance of the original coefficient. -/
theorem ncConnected_small_refinement_exterior_empty {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (huv : u ≤ v) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, ¬ (u ≤ x ∧ x ≤ v) → ¬ p u x)
    (hne : winningJoinCoefficient n q ≠ 0)
    (hsmall : (patternClassPositions q u).card ≤ 4) :
    ∀ x, u ≤ x ∧ x ≤ v := by
  have hn := nonzero_small_refinement_not_crossed q u hne hsmall
  have hsat : ∀ x y, p x y → (u ≤ x ∧ x ≤ v) → (u ≤ y ∧ y ≤ v) := by
    intro x y hxy hx
    by_contra hy
    have hpy : ¬ p u y := hgap y hy
    have hpx : ¬ p u x := fun h => hpy (p.trans h hxy)
    have hqxy : q x y := houtside x y hpx hxy
    have hneU : x ≠ u := by intro h; subst x; exact hpx (p.refl u)
    have hneV : x ≠ v := by intro h; subst x; exact hpx (hle hquv)
    have hux : u < x := by omega
    have hxv : x < v := by omega
    by_cases hyu : y < u
    · exact hn ⟨u,v,y,x,q.refl u,hquv,q.symm hqxy,
        fun h => hpy (hle h),Or.inr ⟨hyu,hux,hxv⟩⟩
    · have hvy : v < y := by omega
      exact hn ⟨u,v,x,y,q.refl u,hquv,hqxy,
        fun h => hpx (hle h),Or.inl ⟨hux,hxv,hvy⟩⟩
  intro x
  by_contra hx
  exact ncConnected_no_saturated_interval p hc (fun z => u ≤ z ∧ z ≤ v)
    (by intros; omega) hsat u x ⟨le_refl u,huv⟩ hx

theorem ncConnected_small_refinement_wrap_adjacent {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (huv : u ≤ v) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, ¬ (u ≤ x ∧ x ≤ v) → ¬ p u x)
    (hne : winningJoinCoefficient n q ≠ 0)
    (hsmall : (patternClassPositions q u).card ≤ 4) :
    u.val = 0 ∧ v.val + 1 = n := by
  have he := ncConnected_small_refinement_exterior_empty p q hc hle u v huv hquv
    houtside hgap hne hsmall
  have hn : 0 < n := by have h := u.isLt; omega
  have h0 := (he ⟨0,hn⟩).1
  have hlast := (he ⟨n-1,by omega⟩).2
  change u.val ≤ 0 at h0
  change n - 1 ≤ v.val at hlast
  constructor <;> omega

/-- A nonadjacent candidate small block therefore contributes zero. -/
theorem winningJoinCoefficient_small_refinement_gap_zero {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (huv : u < v) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, u < x → x < v → ¬ p u x)
    (hsmall : (patternClassPositions q u).card ≤ 4)
    (hnotadj : v.val ≠ u.val + 1) : winningJoinCoefficient n q = 0 := by
  by_contra hne
  exact hnotadj (ncConnected_small_refinement_gap_adjacent p q hc hle u v huv hquv
    houtside hgap hne hsmall)

theorem winningJoinCoefficient_small_refinement_wrap_zero {n : Nat}
    (p q : ColorPattern n) (hc : NCConnected p) (hle : q ≤ p)
    (u v : Fin n) (huv : u ≤ v) (hquv : q u v)
    (houtside : ∀ x y, ¬ p u x → p x y → q x y)
    (hgap : ∀ x, ¬ (u ≤ x ∧ x ≤ v) → ¬ p u x)
    (hsmall : (patternClassPositions q u).card ≤ 4)
    (hnotadj : ¬ (u.val = 0 ∧ v.val + 1 = n)) : winningJoinCoefficient n q = 0 := by
  by_contra hne
  exact hnotadj (ncConnected_small_refinement_wrap_adjacent p q hc hle u v huv hquv
    houtside hgap hne hsmall)

#print axioms ncConnected_small_refinement_gap_adjacent
#print axioms ncConnected_small_refinement_wrap_adjacent
#print axioms winningJoinCoefficient_small_refinement_gap_zero
#print axioms winningJoinCoefficient_small_refinement_wrap_zero
end LC004

import LC004.FourClassTwoShapes
import LC004.OrderedCertificateAssembly

namespace LC004

theorem constraint_pair_interior_closed {n : Nat} (c : ColorPattern n)
    (hc : CertificateConstraint c) {a b x y : Fin n}
    (hab : a < b) (hpair : c a b)
    (hsize : (patternClassPositions c a).card = 2)
    (hx : a < x ∧ x < b) (hxy : c x y) : a < y ∧ y < b := by
  have hno := small_noncrossing_no_alternation c
    (fun i => by rcases hc.1 i with h | h <;> omega) hc.2
  have hya : y ≠ a := by
    intro h
    subst y
    have h := (local_pair_rel_iff c hsize (by omega) hpair x).mp (c.symm hxy)
    omega
  have hyb : y ≠ b := by
    intro h
    subst y
    have h := (local_pair_rel_iff c hsize (by omega) hpair x).mp
      (c.trans hpair (c.symm hxy))
    omega
  by_contra h
  have hcases : y < a ∨ b < y := by omega
  rcases hcases with h | h
  · exact hno y a x b h hx.1 hx.2 ⟨c.symm hxy,hpair⟩
  · exact hno a x b y hx.1 hx.2 h ⟨hpair,hxy⟩

theorem constraint_pair_exterior_closed {n : Nat} (c : ColorPattern n)
    (hc : CertificateConstraint c) {a b x y : Fin n}
    (hab : a < b) (hpair : c a b)
    (hsize : (patternClassPositions c a).card = 2)
    (hx : x < a ∨ b < x) (hxy : c x y) : y < a ∨ b < y := by
  have hya : y ≠ a := by
    intro h
    subst y
    have h := (local_pair_rel_iff c hsize (by omega) hpair x).mp (c.symm hxy)
    omega
  have hyb : y ≠ b := by
    intro h
    subst y
    have h := (local_pair_rel_iff c hsize (by omega) hpair x).mp
      (c.trans hpair (c.symm hxy))
    omega
  by_contra h
  have hy : a < y ∧ y < b := by omega
  have hi := constraint_pair_interior_closed c hc hab hpair hsize hy (c.symm hxy)
  omega

/-- A closed certificate region is winning with its original color equalities. -/
theorem winning_of_certificate_closed_finset {n : Nat} (p c : ColorPattern n)
    (hc : CertificateConstraint c) (href : c ≤ p) (S : Finset (Fin n))
    (hclosed : ∀ x ∈ S, ∀ y, c x y → y ∈ S) :
    WinningColorPattern (restrictColorPattern p (S.orderEmbOfFin rfl)) := by
  classical
  apply (winning_iff_constraint_refinement _).mpr
  refine ⟨restrictColorPattern c (S.orderEmbOfFin rfl), ?_,
    restrictColorPattern_mono href _⟩
  apply certificateConstraint_restrict c hc
  intro i y h
  have hy : y ∈ S := hclosed _ (S.orderEmbOfFin_mem rfl i) y h
  have hr : y ∈ Set.range (S.orderEmbOfFin rfl) := by
    rwa [Finset.range_orderEmbOfFin]
  exact hr

noncomputable def pairInterior {n : Nat} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => a < x ∧ x < b)

noncomputable def pairExterior {n : Nat} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x < a ∨ b < x)

theorem winning_pair_interior {n : Nat} (p c : ColorPattern n)
    (hc : CertificateConstraint c) (href : c ≤ p) {a b : Fin n}
    (hab : a < b) (hpair : c a b)
    (hsize : (patternClassPositions c a).card = 2) :
    WinningColorPattern (restrictColorPattern p ((pairInterior a b).orderEmbOfFin rfl)) := by
  apply winning_of_certificate_closed_finset p c hc href
  intro x hx y hxy
  simp only [pairInterior, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact constraint_pair_interior_closed c hc hab hpair hsize hx hxy

theorem winning_pair_exterior {n : Nat} (p c : ColorPattern n)
    (hc : CertificateConstraint c) (href : c ≤ p) {a b : Fin n}
    (hab : a < b) (hpair : c a b)
    (hsize : (patternClassPositions c a).card = 2) :
    WinningColorPattern (restrictColorPattern p ((pairExterior a b).orderEmbOfFin rfl)) := by
  apply winning_of_certificate_closed_finset p c hc href
  intro x hx y hxy
  simp only [pairExterior, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact constraint_pair_exterior_closed c hc hab hpair hsize hx hxy

#print axioms winning_pair_interior
#print axioms winning_pair_exterior
end LC004

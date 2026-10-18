import LC004.UnionCoefficientIdentity
import LC004.PartitionCounting

namespace LC004

def quadAdjacent : Setoid (Fin 4) :=
  Setoid.ker (fun i => if i.val < 2 then (0 : Nat) else 1)

def quadNested : Setoid (Fin 4) :=
  Setoid.ker (fun i => if i.val = 0 ∨ i.val = 3 then (0 : Nat) else 1)

/-- The two noncrossing pairings of four positions join to the full block. -/
theorem quad_pairings_join_top : quadAdjacent ⊔ quadNested = ⊤ := by
  let j := quadAdjacent ⊔ quadNested
  have h (i : Fin 4) : j 0 i := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact j.refl 0
    · exact (le_sup_left : quadAdjacent ≤ j) (show quadAdjacent 0 1 from rfl)
    · exact j.trans
        ((le_sup_left : quadAdjacent ≤ j) (show quadAdjacent 0 1 from rfl))
        ((le_sup_right : quadNested ≤ j) (show quadNested 1 2 from rfl))
    · exact (le_sup_right : quadNested ≤ j) (show quadNested 0 3 from rfl)
  apply top_unique
  intro a b hab
  exact j.trans (j.symm (h a)) (h b)

/-- Four-block cancellation for arbitrary remaining constraint families.
The remaining application obligation is the explicit four-gap invariance
of their intersection coverage, stated as `hinv`. -/
theorem four_block_barrier_zero {Q : Type*} [Fintype Q] [Lattice Q]
    (ps qs : List Q) (barrier y : Q)
    (hinv : ∀ r,
      (∃ p ∈ joinWitnessLists ps qs, p ≤ r) ↔
      (∃ p ∈ joinWitnessLists ps qs, p ≤ r ⊓ barrier))
    (hy : ¬y ≤ barrier) :
    collectedCoeff (unionTerms (· ⊔ ·)
      ((ps.map fun p => (quadAdjacent,p)) ++ (qs.map fun q => (quadNested,q))))
      ((⊤ : Setoid (Fin 4)),y) = 0 := by
  classical
  letI : Finite (Setoid (Fin 4)) := Finite.of_injective
    (fun s : Setoid (Fin 4) => s.r)
    (fun s t h => Setoid.ext (fun a b => iff_of_eq (congrFun (congrFun h a) b)))
  letI : Fintype (Setoid (Fin 4)) := Fintype.ofFinite _
  have ha : quadAdjacent ≠ quadAdjacent ⊔ quadNested := by
    rw [quad_pairings_join_top]
    intro h
    have bad : quadAdjacent 0 3 := by rw [h]; trivial
    exact Nat.zero_ne_one bad
  have hb : quadNested ≠ quadAdjacent ⊔ quadNested := by
    rw [quad_pairings_join_top]
    intro h
    have bad : quadNested 0 1 := by rw [h]; trivial
    exact Nat.zero_ne_one bad
  simpa only [quad_pairings_join_top] using
    two_branch_barrier_zero quadAdjacent quadNested ps qs ha hb barrier y hinv hy

#print axioms quad_pairings_join_top
#print axioms four_block_barrier_zero

end LC004

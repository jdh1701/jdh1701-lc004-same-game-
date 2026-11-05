import LC004.ChoiceImplicationRecognition

namespace LC004
open scoped Classical

theorem noncrossingBlockFamily_append_swap (A B : List (List Nat)) :
    NoncrossingBlockFamily (A ++ B) ↔ NoncrossingBlockFamily (B ++ A) := by
  unfold NoncrossingBlockFamily
  simp only [List.mem_append,or_comm]

theorem fiveActualCompatible_swap (G H : Finset Nat) (x y : Fin 10) :
    FiveActualCompatible G H x y ↔ FiveActualCompatible H G y x :=
  noncrossingBlockFamily_append_swap _ _

theorem fiveClassSplitFamily_closed {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    ChoiceSolutionsClosed (fiveClassSplitFamily G) := by
  apply choiceSolutionsClosed_of_binary_spec (fiveClassSplitFamily G)
    (fun i j => FiveActualCompatible (G i) (G j)) (fiveClassSplitFamily_spec G)
  intro i j hij
  exact (fiveClass_actual_geometry (G i) (G j) (hG i) (hG j) (hd i j hij)).1

theorem fiveClassSplitFamily_small_edge {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hconn : FiveClassCrossingConnected G) : ChoiceSmallEdge (fiveClassSplitFamily G) := by
  apply choiceCoveredCuts_small_edge
  intro S hS hSc
  obtain ⟨i,hi,j,hj,hcross⟩ := hconn S hS hSc
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  obtain ⟨p,q,hpq⟩ :=
    (fiveClass_actual_geometry (G i) (G j) (hG i) (hG j) (hd i j hij)).2 hcross
  exact ⟨i,hi,j,hj,p,q,fun a ha => hpq _ _ ((fiveClassSplitFamily_spec G a).mp ha i j hij)⟩

/-- Given a separated pair of actual noncrossing split certificates, strong
connectivity of their forbidden-mix graph is exactly uniqueness of that pair.
The graph uses only raw local compatibility, never exact solution projections. -/
theorem fiveClass_survivor_pair_iff_strong {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hconn : FiveClassCrossingConnected G)
    (a b : Fin k → Fin 10) (ha : a ∈ fiveClassSplitFamily G) (hb : b ∈ fiveClassSplitFamily G)
    (hsep : ∀ i, a i ≠ b i) :
    fiveClassSplitFamily G = {a,b} ↔
      ChoiceImplicationStrong (fun i j => FiveActualCompatible (G i) (G j)) a b := by
  exact choice_pair_rigid_iff_implication_strong (fiveClassSplitFamily G)
    (fun i j => FiveActualCompatible (G i) (G j)) (fiveClassSplitFamily_spec G)
    (fun i j x y => fiveActualCompatible_swap (G i) (G j) x y)
    (fiveClassSplitFamily_closed G hG hd) a b ha hb hsep
    (fiveClassSplitFamily_small_edge G hG hd hconn)

#print axioms fiveClass_survivor_pair_iff_strong
end LC004

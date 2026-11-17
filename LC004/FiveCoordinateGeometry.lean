import LC004.FiveEncodedBlocks

namespace LC004
open scoped Classical

noncomputable def fiveCoordinateClassPositions {n k : Nat}
    (e : Fin n ≃ Fin k × Fin 5) (i : Fin k) : Finset Nat :=
  Finset.univ.image (fun u : Fin 5 => (e.symm (i,u)).val)

theorem fiveCoordinateClassPositions_card {n k : Nat}
    (e : Fin n ≃ Fin k × Fin 5) (i : Fin k) :
    (fiveCoordinateClassPositions e i).card = 5 := by
  classical
  rw [fiveCoordinateClassPositions, Finset.card_image_of_injective]
  · exact Fintype.card_fin 5
  · intro u v h
    exact congrArg Prod.snd (e.symm.injective (Fin.ext h))

theorem fiveCoordinateClassPositions_disjoint {n k : Nat}
    (e : Fin n ≃ Fin k × Fin 5) (i j : Fin k) (hij : i ≠ j) :
    Disjoint (fiveCoordinateClassPositions e i) (fiveCoordinateClassPositions e j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hx
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hy
  exact hij (congrArg Prod.fst (e.symm.injective (Fin.ext (hu.trans hv.symm))))

theorem fiveCoordinateClassPositions_sort {n k : Nat}
    (e : Fin n ≃ Fin k × Fin 5)
    (hinc : ∀ i, StrictMono (fun u : Fin 5 => (e.symm (i,u)).val)) (i : Fin k) :
    (fiveCoordinateClassPositions e i).sort (· ≤ ·) =
      (List.finRange 5).map (fun u => (e.symm (i,u)).val) := by
  apply List.Sorted.eq_of_mem_iff (Finset.sort_sorted_lt _)
    ((List.pairwise_lt_finRange 5).map _ (fun _ _ h => hinc i h))
  intro x
  simp [fiveCoordinateClassPositions]

theorem fiveCoordinate_blocks {n k : Nat} (e : Fin n ≃ Fin k × Fin 5)
    (hinc : ∀ i, StrictMono (fun u : Fin 5 => (e.symm (i,u)).val))
    (a : Fin k → Fin 10) :
    (fivePositionBlocks e a).map (List.map Fin.val) =
      fiveClassAssignmentBlocks (fiveCoordinateClassPositions e) a := by
  unfold fivePositionBlocks fiveClassAssignmentBlocks
  rw [List.map_flatMap]
  apply congrArg (List.flatMap · (List.finRange k))
  funext i
  rw [fiveCoordinateClassPositions_sort e hinc i, ← fiveRankBlocks_map]
  simp only [List.map_map, Function.comp_def]

theorem fivePatternCoordinates_increasing {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5)
    (i : Fin (Fintype.card (Quotient p))) :
    StrictMono (fun u : Fin 5 => ((fivePatternCoordinates p hfive).symm (i,u)).val) := by
  let q := (Fintype.equivFin (Quotient p)).symm i
  have hc : (patternQuotientFiber p q).card = 5 := by
    rw [patternQuotientFiber_eq_class]
    exact hfive q.out
  have he : ∀ u : Fin 5, (fivePatternCoordinates p hfive).symm (i,u) =
      (patternQuotientFiber p q).orderEmbOfFin hc u := by
    intro u
    rfl
  intro u v huv
  simpa only [he] using (patternQuotientFiber p q).orderEmbOfFin hc |>.strictMono huv

/-- Exact identification of the original certificate predicate with the
geometric split family used by the cancellation theorem. -/
theorem fiveEncodedNCTuples_eq_splitFamily {n : Nat} (p : ColorPattern n)
    (hfive : ∀ i, (patternClassPositions p i).card = 5) :
    fiveEncodedNCTuples p hfive =
      fiveClassSplitFamily (fiveCoordinateClassPositions (fivePatternCoordinates p hfive)) := by
  classical
  ext a
  simp only [fiveEncodedNCTuples, fiveClassSplitFamily, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [finiteNoncrossing_iff]
  change PatternNoncrossing (Setoid.comap (fivePatternCoordinates p hfive)
    (fiveAssignmentSetoid a)) ↔ _
  rw [fivePositionBlocks_noncrossing_iff, fiveCoordinate_blocks _ (fivePatternCoordinates_increasing p hfive)]

#print axioms fiveEncodedNCTuples_eq_splitFamily
end LC004

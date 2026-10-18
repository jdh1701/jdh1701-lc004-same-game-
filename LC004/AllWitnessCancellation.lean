import LC004.QuadWitnessGeometry

namespace LC004

theorem quad_adjacent_extension {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (s : Setoid (QuadRemainder a b c d)) (hs : PairTriplePartition s)
    (hle : s ≤ adjacentGapRegions (remainderGapIndex a b c d)) :
    PairTriplePartition (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      (quadAdjacent,s)) := by
  apply fullBoardPartition_pairTriple (quadSplitEquiv a b c d hab hbc hcd)
    (quadPosition_strictMono a b c d hab hbc hcd)
    (fun _ _ h => h) (quadAdjacent,s) (quadAdjacent,adjacentGapRegions (remainderGapIndex a b c d))
    quadAdjacent_pairTriple hs ⟨le_rfl,hle⟩
  rw [quad_adjacent_barrier]
  exact noncrossing_inf _ _ (pairGapPartition_noncrossing a b hab)
    (pairGapPartition_noncrossing c d hcd)

theorem quad_nested_extension {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (s : Setoid (QuadRemainder a b c d)) (hs : PairTriplePartition s)
    (hle : s ≤ nestedGapRegions (remainderGapIndex a b c d)) :
    PairTriplePartition (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      (quadNested,s)) := by
  apply fullBoardPartition_pairTriple (quadSplitEquiv a b c d hab hbc hcd)
    (quadPosition_strictMono a b c d hab hbc hcd)
    (fun _ _ h => h) (quadNested,s) (quadNested,nestedGapRegions (remainderGapIndex a b c d))
    quadNested_pairTriple hs ⟨le_rfl,hle⟩
  rw [quad_nested_barrier]
  exact noncrossing_inf _ _ (pairGapPartition_noncrossing a d (lt_trans hab (lt_trans hbc hcd)))
    (pairGapPartition_noncrossing b c hbc)

theorem quad_selected_restriction {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (r : Setoid (Fin n)) (hr : PairTriplePartition r)
    (hle : r ≤ fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      ((⊤ : Setoid (Fin 4)),(⊤ : Setoid (QuadRemainder a b c d)))) :
    PairTriplePartition (Setoid.comap (quadPosition a b c d) r) :=
  pairTriple_comap_saturated _ (quadPosition_strictMono a b c d hab hbc hcd) r hr
    (fullBoardPartition_left_saturated _ r hle)

theorem quad_remainder_restriction {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (r : Setoid (Fin n)) (hr : PairTriplePartition r)
    (hle : r ≤ fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      ((⊤ : Setoid (Fin 4)),(⊤ : Setoid (QuadRemainder a b c d)))) :
    PairTriplePartition (Setoid.comap (fun x : QuadRemainder a b c d => x.val) r) :=
  pairTriple_comap_saturated (fun x : QuadRemainder a b c d => x.val) (fun _ _ h => h) r hr
    (fullBoardPartition_right_saturated _ r hle)

/-- Exact identification of the regional image family with ALL pair/triple
witnesses keeping the four selected positions separate from the remainder. -/
theorem mem_fullBoardFourBlockFamily_iff {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (r : Setoid (Fin n)) :
    r ∈ fullBoardFourBlockFamily a b c d hab hbc hcd ↔
      PairTriplePartition r ∧
      r ≤ fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
        ((⊤ : Setoid (Fin 4)),(⊤ : Setoid (QuadRemainder a b c d))) := by
  let e := quadSplitEquiv a b c d hab hbc hcd
  constructor
  · intro h
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
    change v ∈ regionalFourBlockFamily (remainderGapIndex a b c d) at hv
    simp only [regionalFourBlockFamily,List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hv
      obtain ⟨hs,hle⟩ := (mem_regionalWitnessList _ _).mp hs
      exact ⟨quad_adjacent_extension a b c d hab hbc hcd s hs hle,
        (relabelPartitions e).monotone ((separatedPartition_le_separated_iff _ _).mpr le_top)⟩
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hv
      obtain ⟨hs,hle⟩ := (mem_regionalWitnessList _ _).mp hs
      exact ⟨quad_nested_extension a b c d hab hbc hcd s hs hle,
        (relabelPartitions e).monotone ((separatedPartition_le_separated_iff _ _).mpr le_top)⟩
  · rintro ⟨hr,hle⟩
    let s := Setoid.comap (quadPosition a b c d) r
    let t := Setoid.comap (fun x : QuadRemainder a b c d => x.val) r
    have hs : PairTriplePartition s := quad_selected_restriction a b c d hab hbc hcd r hr hle
    have ht : PairTriplePartition t := quad_remainder_restriction a b c d hab hbc hcd r hr hle
    have he : fullBoardPartition e (s,t) = r := fullBoardPartition_reconstruct e r hle
    rcases pairTriple_fin4_classification s hs with hsa | hsn
    · have hre : r = fullBoardPartition e (quadAdjacent,t) := by rw [← he,hsa]
      have hp : IsPairBlock r a b := by
        rw [hre]
        exact fullBoardPartition_pairBlock_left e (quadAdjacent,t) 0 1 quadAdjacent_pairBlocks.1
      have hq : IsPairBlock r c d := by
        rw [hre]
        exact fullBoardPartition_pairBlock_left e (quadAdjacent,t) 2 3 quadAdjacent_pairBlocks.2
      have hta : t ≤ adjacentGapRegions (remainderGapIndex a b c d) :=
        forced_adjacent_pairs_remainder_refines r hr.1 a b c d hab hbc hcd hp hq
      have hm : t ∈ regionalWitnessList (adjacentGapRegions (remainderGapIndex a b c d)) :=
        (mem_regionalWitnessList _ _).mpr ⟨ht,hta⟩
      apply List.mem_map.mpr
      refine ⟨(quadAdjacent,t),?_,hre.symm⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨t,hm,rfl⟩)
    · have hre : r = fullBoardPartition e (quadNested,t) := by rw [← he,hsn]
      have hp : IsPairBlock r a d := by
        rw [hre]
        exact fullBoardPartition_pairBlock_left e (quadNested,t) 0 3 quadNested_pairBlocks.1
      have hq : IsPairBlock r b c := by
        rw [hre]
        exact fullBoardPartition_pairBlock_left e (quadNested,t) 1 2 quadNested_pairBlocks.2
      have htn : t ≤ nestedGapRegions (remainderGapIndex a b c d) :=
        forced_nested_pairs_remainder_refines r hr.1 a b c d hab hbc hcd hp hq
      have hm : t ∈ regionalWitnessList (nestedGapRegions (remainderGapIndex a b c d)) :=
        (mem_regionalWitnessList _ _).mpr ⟨ht,htn⟩
      apply List.mem_map.mpr
      refine ⟨(quadNested,t),?_,hre.symm⟩
      exact List.mem_append_right _ (List.mem_map.mpr ⟨t,hm,rfl⟩)

/-- Complete specification family, not the executable witness generator. -/
noncomputable def allPairTripleWitnesses (n : Nat) : List (Setoid (Fin n)) :=
  regionalWitnessList ⊤

theorem mem_allPairTripleWitnesses (n : Nat) (r : Setoid (Fin n)) :
    r ∈ allPairTripleWitnesses n ↔ PairTriplePartition r := by
  simp [allPairTripleWitnesses,mem_regionalWitnessList]

/-- Four-position cancellation for the ENTIRE pair/triple witness family.
No coverage or branch-completeness premise remains. -/
theorem all_witness_four_block_zero {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d))
    (hp : ¬p ≤ Setoid.ker (remainderGapIndex a b c d)) :
    collectedCoeff (unionTerms (· ⊔ ·) (allPairTripleWitnesses n))
      (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
        ((⊤ : Setoid (Fin 4)),p)) = 0 := by
  apply fullBoard_four_block_zero_of_coverage a b c d hab hbc hcd p hp
  intro x hx
  constructor
  · rintro ⟨r,hr,hrx⟩
    refine ⟨r,(mem_fullBoardFourBlockFamily_iff a b c d hab hbc hcd r).mpr
      ⟨(mem_allPairTripleWitnesses n r).mp hr,?_⟩,hrx⟩
    exact le_trans (le_trans hrx hx) ((relabelPartitions _).monotone
      ((separatedPartition_le_separated_iff _ _).mpr le_top))
  · rintro ⟨r,hr,hrx⟩
    exact ⟨r,(mem_allPairTripleWitnesses n r).mpr
      ((mem_fullBoardFourBlockFamily_iff a b c d hab hbc hcd r).mp hr).1,hrx⟩

/-- Any surviving coefficient with this four-position block must keep every
other block inside a single cyclic gap. -/
theorem all_witness_four_block_support {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d))
    (hne : collectedCoeff (unionTerms (· ⊔ ·) (allPairTripleWitnesses n))
      (fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
        ((⊤ : Setoid (Fin 4)),p)) ≠ 0) :
    p ≤ Setoid.ker (remainderGapIndex a b c d) := by
  by_contra hp
  exact hne (all_witness_four_block_zero a b c d hab hbc hcd p hp)

end LC004

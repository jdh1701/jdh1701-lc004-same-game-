import LC004.FiveClassRankNormalization

namespace LC004

theorem fivePairRanks_bound (s : Fin 10) (i : Nat) (hi : i ∈ fivePairRanks s) : i < 5 := by
  obtain ⟨u,v,_,he⟩ := fivePairRanks_valid s
  rw [he] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · exact u.isLt
  · exact v.isLt

/-- Split labels are ranks within their own class, so the same label is used
regardless of which other class is selected for pairwise normalization. -/
theorem fiveSplitBlocks_map (f : Nat → Nat) (g : List Nat) (hg : g.length = 5)
    (s : Fin 10) :
    fiveSplitBlocks (g.map f) s = (fiveSplitBlocks g s).map (List.map f) := by
  have hm (i : Nat) (hi : i < 5) : (g.map f)[i]! = f (g[i]!) := by
    have hib : i < g.length := by omega
    have him : i < (g.map f).length := by simpa using hib
    rw [getElem!_pos (g.map f) i him, getElem!_pos g i hib, List.getElem_map]
  have hp : (fivePairRanks s).map (fun i => (g.map f)[i]!) =
      ((fivePairRanks s).map (fun i => g[i]!)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hm i (fivePairRanks_bound s i hi)
  have ht : ((List.range 5).filter (fun i => !(fivePairRanks s).contains i)).map
      (fun i => (g.map f)[i]!) =
      (((List.range 5).filter (fun i => !(fivePairRanks s).contains i)).map
        (fun i => g[i]!)).map f := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hm i (List.mem_range.mp (List.mem_filter.mp hi).1)
  simpa only [fiveSplitBlocks, List.map_cons, List.map_nil] using congrArg₂ List.cons hp
    (congrArg (fun xs => [xs]) ht)

def FiveActualCompatible (G H : Finset Nat) (x y : Fin 10) : Prop :=
  NoncrossingBlockFamily
    (fiveSplitBlocks (G.sort (· ≤ ·)) x ++ fiveSplitBlocks (H.sort (· ≤ ·)) y)

/-- The finite relation theorem now applies to arbitrary actual five-point
classes, without a normal-form hypothesis supplied by the caller. -/
theorem fiveClass_actual_geometry (G H : Finset Nat)
    (hG : G.card = 5) (hH : H.card = 5) (hd : Disjoint G H) :
    ChoiceRelationClosed (FiveActualCompatible G H) ∧
      (BlocksCross (G.sort (· ≤ ·)) (H.sort (· ≤ ·)) →
        ∃ p q : Fin 10, ∀ x y, FiveActualCompatible G H x y → x = p ∨ y = q) := by
  obtain ⟨f,g,hf,hg,hgm,hhm⟩ := five_classes_rank_normal_form G H hG hH hd
  have hgl : g.length = 5 := by
    have h := congrArg List.length hgm
    simpa [hG] using h
  have hhl : (fiveOtherRanks g).length = 5 := by
    have h := congrArg List.length hhm
    simpa [hH] using h
  have he : ∀ x y, FiveActualCompatible G H x y ↔
      FivePlacedCompatible f g (fiveOtherRanks g) x y := by
    intro x y
    unfold FiveActualCompatible FivePlacedCompatible
    rw [← hgm, ← hhm, fiveSplitBlocks_map f g hgl,
      fiveSplitBlocks_map f _ hhl, List.map_append]
  obtain ⟨hc,hcover⟩ := fiveClass_placed_geometry f hf g hg
  refine ⟨(choiceRelationClosed_congr he).mpr hc, ?_⟩
  intro hcross
  have hx : BlocksCross (g.map f) ((fiveOtherRanks g).map f) := by
    simpa only [hgm,hhm] using hcross
  obtain ⟨p,q,hpq⟩ := hcover hx
  exact ⟨p,q, fun x y hxy => hpq x y ((he x y).mp hxy)⟩

#print axioms fiveSplitBlocks_map
#print axioms fiveClass_actual_geometry
end LC004

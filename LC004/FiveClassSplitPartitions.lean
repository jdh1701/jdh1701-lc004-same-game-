import LC004.FiveClassSplitJoins

namespace LC004
open scoped Classical

/-- The rank-level split really partitions all five positions. -/
theorem fiveSplit_rank_partition : ∀ s : Fin 10,
    (fiveSplitBlocks [0,1,2,3,4] s).flatten.Perm [0,1,2,3,4] := by
  decide +kernel

theorem fiveSplit_rank_sizes : ∀ s : Fin 10, ∀ b ∈ fiveSplitBlocks [0,1,2,3,4] s,
    b.length = 2 ∨ b.length = 3 := by
  decide +kernel

theorem five_list_index_map (g : List Nat) (hg : g.length = 5) :
    (List.range 5).map (fun i => g[i]!) = g := by
  apply List.ext_getElem
  · simp [hg]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range]
    exact getElem!_pos g i hi'

/-- Every selected split covers its actual class exactly once, including
internally crossing choices that will later be removed by noncrossing. -/
theorem fiveSplit_partition (g : List Nat) (hg : g.length = 5) (s : Fin 10) :
    (fiveSplitBlocks g s).flatten.Perm g := by
  let f : Nat → Nat := fun i => g[i]!
  have hm : ([0,1,2,3,4] : List Nat).map f = g := five_list_index_map g hg
  have he := fiveSplitBlocks_map f [0,1,2,3,4] rfl s
  rw [hm] at he
  rw [he, ← List.map_flatten]
  simpa only [hm] using (fiveSplit_rank_partition s).map f

theorem fiveSplit_sizes (g : List Nat) (hg : g.length = 5) (s : Fin 10)
    (b : List Nat) (hb : b ∈ fiveSplitBlocks g s) : b.length = 2 ∨ b.length = 3 := by
  let f : Nat → Nat := fun i => g[i]!
  have hm : ([0,1,2,3,4] : List Nat).map f = g := five_list_index_map g hg
  have he := fiveSplitBlocks_map f [0,1,2,3,4] rfl s
  rw [hm] at he
  rw [he] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  simpa only [List.length_map] using fiveSplit_rank_sizes s c hc

/-- Exact cover for the entire selected family. The right-hand side enumerates
all actual class positions, not split labels or abstract CSP values. -/
theorem fiveClassAssignmentBlocks_exactCover {k : Nat} (G : Fin k → Finset Nat)
    (hG : ∀ i, (G i).card = 5) (a : Fin k → Fin 10) :
    (fiveClassAssignmentBlocks G a).flatten.Perm
      ((List.finRange k).flatMap fun i => (G i).sort (· ≤ ·)) := by
  unfold fiveClassAssignmentBlocks
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  apply List.Perm.flatMap_left
  intro i _
  simpa only [← List.flatten_eq_flatMap] using
    fiveSplit_partition _ (by simpa only [Finset.length_sort] using hG i) (a i)

theorem fiveClassAssignmentBlocks_sizes {k : Nat} (G : Fin k → Finset Nat)
    (hG : ∀ i, (G i).card = 5) (a : Fin k → Fin 10) :
    ∀ b ∈ fiveClassAssignmentBlocks G a, b.length = 2 ∨ b.length = 3 := by
  intro b hb
  obtain ⟨i,_,hbi⟩ := List.mem_flatMap.mp hb
  exact fiveSplit_sizes _ (by simpa only [Finset.length_sort] using hG i) (a i) b hbi

/-- Complete signed face-sum law with survival expressed as a partition join.
The identification with winningJoinCoefficient is a separate theorem. -/
theorem fiveClassSplitFamily_join_survival_law {k : Nat} [Nontrivial (Fin k)]
    (G : Fin k → Finset Nat) (hG : ∀ i, (G i).card = 5)
    (hd : ∀ i j, i ≠ j → Disjoint (G i) (G j)) (hconn : FiveClassCrossingConnected G) :
    faceAlternatingSum (facetFaces (choiceFacets (fiveClassSplitFamily G))) =
      if (∃ a b, fiveClassSplitFamily G = {a,b} ∧
        fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b = fiveClassBaseSetoid k) then -1 else 0 := by
  classical
  have he : (∃ a b, fiveClassSplitFamily G = {a,b} ∧
      fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b = fiveClassBaseSetoid k) ↔
      (∃ a b, fiveClassSplitFamily G = {a,b} ∧ ∀ i, a i ≠ b i) := by
    simp only [fiveAssignmentSetoid_join_eq_base_iff]
  have hc := fiveClassSplitFamily_alternatingSum_classification G hG hd hconn
  by_cases hs : ∃ a b, fiveClassSplitFamily G = {a,b} ∧ ∀ i, a i ≠ b i
  · rw [if_pos hs] at hc
    rw [if_pos (he.mpr hs)]
    exact hc
  · rw [if_neg hs] at hc
    rw [if_neg (fun h => hs (he.mp h))]
    exact hc

#print axioms fiveClassAssignmentBlocks_exactCover
#print axioms fiveClassSplitFamily_join_survival_law
end LC004

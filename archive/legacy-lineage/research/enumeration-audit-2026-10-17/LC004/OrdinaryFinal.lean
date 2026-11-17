import LC004.OrdinaryCommutation
import LC004.CertifiedPaths

namespace LC004

/-- The shortest cell representative: light runs have length one and heavy
runs length two. This supplies an ordinary word for every normalized state. -/
def expandRuns : RunState → RawState
  | [] => []
  | (c,b) :: xs => if b then c :: c :: expandRuns xs else c :: expandRuns xs

theorem encode_expandRuns {s : RunState} (hn : Normalized s) :
    encode (expandRuns s) = s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨c,b⟩
      have ht := ih (normalized_tail hn)
      cases xs with
      | nil => cases b <;> simp [expandRuns, encode, pushColor]
      | cons y ys =>
          rcases y with ⟨d,e⟩
          have hcd : c ≠ d := hn.1
          cases b with
          | false =>
              change pushColor c (encode (expandRuns ((d,e)::ys))) = _
              rw [ht]
              simp [pushColor, hcd]
          | true =>
              change pushColor c (pushColor c (encode (expandRuns ((d,e)::ys)))) = _
              rw [ht]
              simp [pushColor, hcd]

/-- Unconditional correspondence for every ordinary word and every index list. -/
theorem ordinary_path_iff (w : RawState) (moves : List Nat) :
    ordinaryFollow ordinaryStepAt w moves = some [] ↔
      SuccessfulPath (encode w) moves :=
  ordinarySuccessfulPath_iff ordinaryStepAt ordinaryStepAt_map_encode w moves

theorem ordinary_solvable_iff (w : RawState) :
    OrdinarySolvable ordinaryStepAt w ↔ RunSolvable (encode w) :=
  ordinarySolvable_iff ordinaryStepAt ordinaryStepAt_map_encode w

/-- The original unique-first/unique-path result now applies directly to
maximal equal-colour cell runs; no commuting hypothesis remains. -/
theorem ordinary_unique_first_iff_path (w : RawState) (hne : w ≠ []) :
    OrdinaryUniqueSuccessfulFirst ordinaryStepAt w ↔
      OrdinaryUniqueSuccessfulPath ordinaryStepAt w :=
  ordinary_unique_first_iff_path_of_commute ordinaryStepAt
    ordinaryStepAt_map_encode w hne

theorem ordinary_unique_path_eq_medianPath (w : RawState) (moves : List Nat)
    (hu : OrdinaryUniqueSuccessfulPath ordinaryStepAt w)
    (hp : ordinaryFollow ordinaryStepAt w moves = some []) :
    moves = medianPath (encode w).length := by
  exact unique_successful_path_eq_medianPath (encode_normalized w)
    ((ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode w).mp hu)
    ((ordinary_path_iff w moves).mp hp)

theorem ordinary_unique_path_color_palindrome (w : RawState) (hne : w ≠ [])
    (hu : OrdinaryUniqueSuccessfulPath ordinaryStepAt w) :
    ((encode w).map Prod.fst).reverse = (encode w).map Prod.fst := by
  apply unique_successful_path_color_palindrome (encode_normalized w)
  · exact fun h => hne ((encode_eq_nil_iff w).mp h)
  · exact (ordinaryUniquePath_iff ordinaryStepAt ordinaryStepAt_map_encode w).mp hu

/-- A certified exact finite set of all ordinary successful indexed paths. -/
def ordinarySolutionPaths (w : RawState) : Finset (List Nat) :=
  solutionPaths (encode w)

theorem mem_ordinarySolutionPaths_iff (w : RawState) (moves : List Nat) :
    moves ∈ ordinarySolutionPaths w ↔
      ordinaryFollow ordinaryStepAt w moves = some [] := by
  exact (mem_solutionPaths_iff (encode w) moves).trans (ordinary_path_iff w moves).symm

/-- Replacing any heavy run by a different length >=2 preserves precisely
the successful index sequences, not merely whether the word is solvable. -/
theorem ordinary_paths_invariant_of_encode_eq (w v : RawState)
    (he : encode w = encode v) (moves : List Nat) :
    ordinaryFollow ordinaryStepAt w moves = some [] ↔
      ordinaryFollow ordinaryStepAt v moves = some [] := by
  rw [ordinary_path_iff, ordinary_path_iff, he]

theorem ordinary_expansion_path_iff (s : RunState) (hn : Normalized s)
    (moves : List Nat) :
    ordinaryFollow ordinaryStepAt (expandRuns s) moves = some [] ↔
      SuccessfulPath s moves := by
  rw [ordinary_path_iff, encode_expandRuns hn]

theorem ordinary_path_count_invariant_of_encode_eq (w v : RawState)
    (he : encode w = encode v) :
    (ordinarySolutionPaths w).card = (ordinarySolutionPaths v).card := by
  simp only [ordinarySolutionPaths, he]

#print axioms ordinaryStepAt_map_encode
#print axioms ordinary_path_iff
#print axioms ordinary_unique_first_iff_path
#print axioms ordinary_unique_path_eq_medianPath
#print axioms mem_ordinarySolutionPaths_iff

end LC004

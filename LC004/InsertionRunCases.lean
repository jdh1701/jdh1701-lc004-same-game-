import LC004.FullSimulation

namespace LC004

/-- Increasing run heaviness without changing the run-color skeleton
    preserves solvability. This is an explicit application of an
    existing, previously formalized simulation theorem. -/
theorem insertion_existing_run_solvable
    {s t : RunState}
    (hst : Heavier s t)
    (hs : Solvable Step (fun x => x = []) s) :
    Solvable Step (fun x => x = []) t := by
  exact sameGame_solvable_mono_full hst hs

/-- Inserting a fresh heavy run whose removal does not merge its
    neighboring runs preserves solvability by one actual Same Game move. -/
theorem insertion_fresh_run_solvable
    (pre post : RunState) (c : Nat)
    (hboundary : ∀ p q,
       pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1)
    (hs : Solvable Step (fun x => x = []) (pre ++ post)) :
    Solvable Step (fun x => x = []) (pre ++ (c,true) :: post) := by
  exact Solvable.move (Step.noMerge hboundary) hs

end LC004

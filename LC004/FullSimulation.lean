import LC004.RunState
import LC004.Transition
import LC004.Simulation
import LC004.DeleteSimulation
import LC004.NoMergeFull

namespace LC004

theorem deleteSimulation_full : DeleteSimulation := by
  intro s t u hst hstep
  cases hstep with
  | merge =>
      exact deleteSimulation_merge hst
  | @noMerge pre post c hboundary =>
      exact deleteSimulation_noMerge_full hboundary hst

theorem sameGame_solvable_mono_full
    {s t : RunState}
    (hst : Heavier s t)
    (hs : Solvable Step (fun x => x = []) s) :
    Solvable Step (fun x => x = []) t := by
  exact sameGame_solvable_mono deleteSimulation_full hst hs

end LC004

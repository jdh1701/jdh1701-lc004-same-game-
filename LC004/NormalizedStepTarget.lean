import LC004.RunState
import LC004.Normalized
import LC004.Transition

namespace LC004

/-- Semantic target: every legal abstract transition from a normalized run
state remains normalized. -/
theorem normalized_step
    {s t : RunState}
    (hn : Normalized s)
    (hs : Step s t) :
    Normalized t := by
  cases hs with
  | @noMerge pre post c hboundary =>
      -- Deleting a run either exposes no pair or a pair certified unequal by hboundary.
      sorry
  | @merge pre post c d bp bq =>
      -- A normalized source has c != d on both sides of the deleted d-run.
      -- Need to show the merged c-run also differs from the outer boundaries.
      sorry

end LC004

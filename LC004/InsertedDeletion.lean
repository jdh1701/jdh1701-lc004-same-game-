import LC004.NormalizedDirectional
import LC004.IndexedMove

namespace LC004

/-- If the concatenation of two contexts is normalized, then a freshly
inserted heavy run between them can be deleted by a no-merge indexed step. -/
theorem indexedStep_delete_inserted_of_normalized
    {left right : RunState} {c : Nat}
    (hn : Normalized (left ++ right)) :
    IndexedStep
      (left ++ (c,true) :: right)
      left.length
      (left ++ right) := by
  apply IndexedStep.noMerge
  exact normalized_boundary_of_append hn

end LC004

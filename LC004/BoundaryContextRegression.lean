import LC004.ExecutableStep

namespace LC004

/-- A deletion at the prefix boundary can merge a prefix run with a
suffix run. An unrestricted prefix-stripping identity is therefore false. -/
theorem prefix_boundary_stripping_counterexample :
    stepAt ([(0, false)] ++ [(1, true), (0, false)]) 1 ≠
      (stepAt [(1, true), (0, false)] 0).map
        (fun t => [(0, false)] ++ t) := by
  decide

#print axioms prefix_boundary_stripping_counterexample

end LC004

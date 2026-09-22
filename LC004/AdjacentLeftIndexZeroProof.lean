import LC004.AdjacentLeftIndexZeroStrip
import LC004.ExecutableStep

namespace LC004

/-- Exact-boundary executable law.  A move selected immediately after an
unchanged prefix is exactly the local index-zero move with that prefix
reattached to the successor. -/
theorem adjacentLeftIndexZeroExecutable_proved :
    AdjacentLeftIndexZeroExecutable := by
  intro prefix s
  induction prefix with
  | nil =>
      simp
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases s with
          | nil =>
              simp [stepAt]
          | cons y ys =>
              rcases x with ⟨cx,bx⟩
              rcases y with ⟨cy,by⟩
              cases by <;> simp [stepAt]
      | cons y ys =>
          have hne : (y :: ys).length ≠ 0 := by simp
          rw [List.cons_append]
          have hstep :=
            stepAt_cons_nonzero_tail x ((y :: ys) ++ s)
              ((y :: ys).length) hne
          rw [hstep]
          have ih' := ih (s := s)
          rw [ih']
          simp [Option.map_map, Function.comp_def, List.cons_append]

theorem adjacentLeftIndexZeroStrip_proved :
    AdjacentLeftIndexZeroStrip :=
  adjacentLeftIndexZeroStrip_of_executable
    adjacentLeftIndexZeroExecutable_proved


theorem adjacentLeftNoMergeExchange_proved :
    AdjacentLeftNoMergeExchange :=
  adjacentLeftNoMergeExchange_of_strip
    adjacentLeftIndexZeroStrip_proved
    adjacentLeftIndexZeroExecutable_proved

end LC004

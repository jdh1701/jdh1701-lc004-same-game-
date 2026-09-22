import LC004.IndexedMove

namespace LC004

/-- Every retained move index points to an actual run of the source state. -/
theorem indexedStep_index_lt
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    i < s.length := by
  cases h with
  | @noMerge pre post c hboundary =>
      simp
  | @merge pre post c d bp bq =>
      simp
      omega

end LC004

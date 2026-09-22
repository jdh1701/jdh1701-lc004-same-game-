import LC004.RunState

namespace LC004

theorem exists_split_last {α : Type*} (l : List α) (h : l ≠ []) :
    ∃ left a, l = left ++ [a] ∧ l.getLast? = some a := by
  refine ⟨l.dropLast, l.getLast h, ?_, ?_⟩
  · exact (List.dropLast_append_getLast h).symm
  · simp [List.getLast?_eq_getLast, h]

end LC004

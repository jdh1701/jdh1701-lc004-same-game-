import LC004.RunState

namespace LC004

theorem exists_split_last {α : Type*} (l : List α) (h : l ≠ []) :
    ∃ left a, l = left ++ [a] ∧ l.getLast? = some a := by
  induction l with
  | nil => contradiction
  | cons x xs =>
      cases xs with
      | nil =>
          exact ⟨[], x, by simp, by simp⟩
      | cons y ys =>
          have htail : y :: ys ≠ [] := by simp
          obtain ⟨left, a, heq, hlast⟩ := exists_split_last (y::ys) htail
          refine ⟨x::left, a, ?_, ?_⟩
          · simp [heq]
          · simpa [heq] using hlast

end LC004

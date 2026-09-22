import LC004.RunState
import LC004.Normalized

namespace LC004

/-- Normalization of a concatenation is exactly normalization of both pieces
plus inequality at the newly adjacent boundary. -/
theorem normalized_append_iff (xs ys : RunState) :
    Normalized (xs ++ ys) ↔
      Normalized xs ∧ Normalized ys ∧
      (∀ p q, xs.getLast? = some p → ys.head? = some q → p.1 ≠ q.1) := by
  induction xs with
  | nil =>
      simp [Normalized]
  | cons x rest ih =>
      cases rest with
      | nil =>
          cases ys with
          | nil => simp [Normalized]
          | cons y ys' =>
              rcases x with ⟨c,b⟩
              rcases y with ⟨d,e⟩
              simp [Normalized]
      | cons y rest' =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp only [List.cons_append, Normalized]
          rw [ih]
          constructor
          · intro h
            exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
          · intro h
            exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

end LC004

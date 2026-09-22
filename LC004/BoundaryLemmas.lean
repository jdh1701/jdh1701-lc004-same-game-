import LC004.RunState
import LC004.HeavierLemmas

namespace LC004

theorem heavier_head_color
    {c d : Nat} {b e : Bool} {xs ys : RunState}
    (h : Heavier ((c,b)::xs) ((d,e)::ys)) :
    c = d := by
  simpa [Heavier] using h.1

theorem heavier_head_tail
    {c d : Nat} {b e : Bool} {xs ys : RunState}
    (h : Heavier ((c,b)::xs) ((d,e)::ys)) :
    Heavier xs ys := by
  simpa [Heavier] using h.2.2

theorem heavier_singleton_color
    {c d : Nat} {b e : Bool}
    (h : Heavier [(c,b)] [(d,e)]) :
    c = d := by
  simpa [Heavier] using h.1

theorem heavier_head_shape
    {c : Nat} {b : Bool} {xs t : RunState}
    (h : Heavier ((c,b)::xs) t) :
    ∃ e ys, t = (c,e)::ys ∧ (b → e) ∧ Heavier xs ys := by
  cases t with
  | nil => simp [Heavier] at h
  | cons y ys =>
      rcases y with ⟨d,e⟩
      simp only [Heavier] at h
      rcases h with ⟨hcd, hbit, htail⟩
      subst d
      exact ⟨e, ys, rfl, hbit, htail⟩

theorem heavier_last_color
    {pre pre' : RunState} {c d : Nat} {b e : Bool}
    (h : Heavier (pre ++ [(c,b)]) (pre' ++ [(d,e)])) :
    c = d := by
  induction pre generalizing pre' with
  | nil =>
      cases pre' with
      | nil => simpa [Heavier] using h.1
      | cons y ys =>
          simp [Heavier] at h
  | cons x xs ih =>
      cases pre' with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨cx,bx⟩
          rcases y with ⟨cy,byy⟩
          simp only [List.cons_append, Heavier] at h
          exact ih h.2.2

end LC004

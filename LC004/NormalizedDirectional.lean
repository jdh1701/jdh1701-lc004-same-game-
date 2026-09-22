import LC004.RunState
import LC004.Normalized

namespace LC004

theorem normalized_append_of
    {xs ys : RunState}
    (hxs : Normalized xs)
    (hys : Normalized ys)
    (hb : ∀ p q, xs.getLast? = some p → ys.head? = some q → p.1 ≠ q.1) :
    Normalized (xs ++ ys) := by
  induction xs with
  | nil => simpa using hys
  | cons x rest ih =>
      cases rest with
      | nil =>
          cases ys with
          | nil => simpa [Normalized]
          | cons y ys' =>
              rcases x with ⟨c,b⟩
              rcases y with ⟨d,e⟩
              have hcd : c ≠ d := by
                exact hb (c,b) (d,e) (by simp) (by simp)
              simpa [Normalized] using And.intro hcd hys
      | cons y rest' =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp only [Normalized] at hxs ⊢
          exact ⟨hxs.1, ih hxs.2 hys (by
            intro p q hp hq
            apply hb p q
            · simpa using hp
            · exact hq)⟩

theorem normalized_prefix_of_append
    {xs ys : RunState}
    (h : Normalized (xs ++ ys)) :
    Normalized xs := by
  induction xs with
  | nil => trivial
  | cons x rest ih =>
      cases rest with
      | nil => simp [Normalized]
      | cons y rest' =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp only [List.cons_append, Normalized] at h ⊢
          exact ⟨h.1, ih h.2⟩

end LC004

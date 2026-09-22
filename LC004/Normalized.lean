import LC004.RunState

namespace LC004

/-- A run state is normalized when adjacent runs never have the same color. -/
def Normalized : RunState → Prop
  | [] => True
  | [_] => True
  | (c,_) :: (d,b) :: xs => c ≠ d ∧ Normalized ((d,b)::xs)

theorem normalized_tail {x : Nat × Bool} {xs : RunState}
    (h : Normalized (x::xs)) : Normalized xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
      rcases x with ⟨c,b⟩
      rcases y with ⟨d,e⟩
      simpa [Normalized] using h.2

/-- Heavier preserves the exact color skeleton, hence normalization. -/
theorem normalized_heavier
    {s t : RunState}
    (hn : Normalized s)
    (h : Heavier s t) :
    Normalized t := by
  induction s generalizing t with
  | nil =>
      cases t <;> simp [Heavier, Normalized] at h ⊢
  | cons x xs ih =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp only [Heavier] at h
          rcases h with ⟨hcd, hbit, htail⟩
          subst d
          cases xs with
          | nil =>
              cases ys <;> simp [Heavier, Normalized] at htail ⊢
          | cons z zs =>
              rcases z with ⟨f,g⟩
              cases ys with
              | nil => simp [Heavier] at htail
              | cons w ws =>
                  rcases w with ⟨k,m⟩
                  simp only [Heavier] at htail
                  have hfk : f = k := htail.1
                  subst k
                  simp only [Normalized] at hn ⊢
                  exact ⟨hn.1, ih hn.2 htail⟩

end LC004

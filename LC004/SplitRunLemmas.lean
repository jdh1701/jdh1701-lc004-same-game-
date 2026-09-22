import LC004.RunState
import LC004.HeavierLemmas

namespace LC004

/-- General structural split: a heavier state has the same run color at the
same position, with a bit at least as heavy as the source bit. -/
theorem heavier_split_run
    (pre post : RunState) (c : Nat) (b : Bool) {t : RunState}
    (h : Heavier (pre ++ (c,b) :: post) t) :
    ∃ pre' post' (e : Bool),
      t = pre' ++ (c,e) :: post' ∧
      (b = true → e = true) ∧
      Heavier pre pre' ∧
      Heavier post post' := by
  induction pre generalizing t with
  | nil =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases y with ⟨d,e⟩
          simp only [List.nil_append, Heavier] at h
          rcases h with ⟨hcd, hbit, htail⟩
          subst d
          exact ⟨[], ys, e, by simp, hbit, by simp [Heavier], htail⟩
  | cons x xs ih =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨cx,bx⟩
          rcases y with ⟨cy,byy⟩
          simp only [List.cons_append, Heavier] at h
          rcases h with ⟨hcolor, hbit, htail⟩
          obtain ⟨pre', post', e, ht, hb, hp, hs⟩ := ih htail
          subst cy
          refine ⟨(cx,byy)::pre', post', e, ?_, hb, ?_, hs⟩
          · simpa [ht]
          · simp only [Heavier]
            exact ⟨trivial, hbit, hp⟩

end LC004

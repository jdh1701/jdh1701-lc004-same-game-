import LC004.RunState

namespace LC004

theorem heavier_append {a b c d : RunState}
    (hab : Heavier a b) (hcd : Heavier c d) :
    Heavier (a ++ c) (b ++ d) := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simpa using hcd
      | cons y ys => simp [Heavier] at hab
  | cons x xs ih =>
      cases b with
      | nil => simp [Heavier] at hab
      | cons y ys =>
          rcases x with ⟨cx,bx⟩
          rcases y with ⟨cy,byy⟩
          simp only [Heavier] at hab ⊢
          exact ⟨hab.1, hab.2.1, ih hab.2.2⟩

theorem heavier_split_heavy
    (pre post : RunState) (c : Nat) {t : RunState}
    (h : Heavier (pre ++ (c,true) :: post) t) :
    ∃ pre' post',
      t = pre' ++ (c,true) :: post' ∧
      Heavier pre pre' ∧ Heavier post post' := by
  induction pre generalizing t with
  | nil =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases y with ⟨d,e⟩
          simp only [List.nil_append, Heavier] at h
          rcases h with ⟨hcd, hbit, htail⟩
          subst d
          have he : e = true := by
            cases e <;> simp_all
          subst e
          exact ⟨[], ys, by simp, by simp [Heavier], htail⟩
  | cons x xs ih =>
      cases t with
      | nil => simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨cx,bx⟩
          rcases y with ⟨cy,byy⟩
          simp only [List.cons_append, Heavier] at h
          rcases h with ⟨hcolor, hbit, htail⟩
          obtain ⟨pre', post', ht, hp, hs⟩ := ih htail
          subst cy
          subst ys
          refine ⟨(cx,byy)::pre', post', ?_, ?_, hs⟩
          · simp
          · simp only [Heavier]
            exact ⟨trivial, hbit, hp⟩

end LC004

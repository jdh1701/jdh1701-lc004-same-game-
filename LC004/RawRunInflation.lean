import LC004.RawIsolatedInsertion

namespace LC004

/-- Replace every raw cell by one or more copies of its color.
This preserves the maximal-run skeleton and can only lengthen runs. -/
inductive RawInflates {q : Nat} : List (Fin q) → List (Fin q) → Prop where
  | nil : RawInflates [] []
  | cons (a : Fin q) (extra : Nat) {xs ys : List (Fin q)} :
      RawInflates xs ys →
      RawInflates (a :: xs) (List.replicate (extra + 1) a ++ ys)

theorem raw_inflates_refl {q : Nat} (w : List (Fin q)) : RawInflates w w := by
  induction w with
  | nil => exact RawInflates.nil
  | cons a xs ih => simpa using RawInflates.cons a 0 ih

theorem raw_inflates_append {q : Nat} {u u' v v' : List (Fin q)}
    (hu : RawInflates u u') (hv : RawInflates v v') :
    RawInflates (u ++ v) (u' ++ v') := by
  induction hu with
  | nil => simpa using hv
  | cons a k h ih =>
      simpa only [List.cons_append, List.append_assoc] using RawInflates.cons a k ih

/-- Split an expansion at any source-word boundary. -/
theorem raw_inflates_split {q : Nat} (u v : List (Fin q))
    {w : List (Fin q)} (h : RawInflates (u ++ v) w) :
    ∃ u' v', w = u' ++ v' ∧ RawInflates u u' ∧ RawInflates v v' := by
  induction u generalizing w with
  | nil => exact ⟨[], w, by simp, RawInflates.nil, h⟩
  | cons a xs ih =>
      cases h with
      | cons a k htail =>
          obtain ⟨u', v', heq, hu, hv⟩ := ih htail
          refine ⟨List.replicate (k + 1) a ++ u', v', ?_,
            RawInflates.cons a k hu, hv⟩
          rw [heq, List.append_assoc]

theorem raw_inflates_replicate {q : Nat} (a : Fin q) (n : Nat)
    {w : List (Fin q)} (h : RawInflates (List.replicate n a) w) :
    ∃ m, n ≤ m ∧ w = List.replicate m a := by
  induction n generalizing w with
  | zero =>
      cases h
      exact ⟨0, by omega, rfl⟩
  | succ n ih =>
      rw [List.replicate_succ] at h
      cases h with
      | cons a k htail =>
          obtain ⟨m, hnm, heq⟩ := ih htail
          refine ⟨k + 1 + m, by omega, ?_⟩
          rw [heq]
          exact (List.replicate_add (k + 1) m a).symm

theorem raw_inflates_head {q : Nat} {u v : List (Fin q)}
    (h : RawInflates u v) : v.head? = u.head? := by
  cases h with
  | nil => rfl
  | cons a k h => simp [List.replicate_succ]

theorem raw_inflates_reverse {q : Nat} {u v : List (Fin q)}
    (h : RawInflates u v) : RawInflates u.reverse v.reverse := by
  induction h with
  | nil => exact RawInflates.nil
  | cons a k h ih =>
      have hs : RawInflates [a] (List.replicate (k + 1) a) := by
        simpa using RawInflates.cons a k RawInflates.nil
      simpa only [List.reverse_cons, List.reverse_append, List.reverse_replicate] using
        raw_inflates_append ih hs

theorem raw_inflates_last {q : Nat} {u v : List (Fin q)}
    (h : RawInflates u v) : v.getLast? = u.getLast? := by
  simpa only [List.head?_reverse] using raw_inflates_head (raw_inflates_reverse h)

/-- Every genuine maximal-run move is simulated after inflation.
The expanded deleted run is still maximal because boundary colors
are preserved, and its length remains at least two. -/
theorem raw_inflates_step {q : Nat} {u v u' : List (Fin q)}
    (hi : RawInflates u u') (hs : RawMaxStep u v) :
    ∃ v', RawMaxStep u' v' ∧ RawInflates v v' := by
  cases hs with
  | delete left right a n hn hleft hright =>
      have hi' : RawInflates (left ++ (List.replicate n a ++ right)) u' := by
        simpa only [List.append_assoc] using hi
      obtain ⟨left', tail', hu, hl, ht⟩ := raw_inflates_split left _ hi'
      obtain ⟨mid', right', htail, hm, hr⟩ :=
        raw_inflates_split (List.replicate n a) right ht
      obtain ⟨m, hnm, hmid⟩ := raw_inflates_replicate a n hm
      have hleft' : left'.getLast? ≠ some a := by
        rw [raw_inflates_last hl]
        exact hleft
      have hright' : right'.head? ≠ some a := by
        rw [raw_inflates_head hr]
        exact hright
      have hstep := RawMaxStep.delete left' right' a m (by omega) hleft' hright'
      have heq : u' = left' ++ List.replicate m a ++ right' := by
        rw [hu, htail, hmid]
        simp only [List.append_assoc]
      refine ⟨left' ++ right', ?_, raw_inflates_append hl hr⟩
      exact Eq.mpr (congrArg (fun src => RawMaxStep src (left' ++ right')) heq) hstep

theorem raw_inflates_path {q : Nat} {u v : List (Fin q)}
    (h : RawMaxErases u v) {u' : List (Fin q)} (hi : RawInflates u u') :
    ∃ v', RawMaxErases u' v' ∧ RawInflates v v' := by
  induction h generalizing u' with
  | refl w => exact ⟨u', RawMaxErases.refl u', hi⟩
  | next hstep hrest ih =>
      obtain ⟨middle, hs, hm⟩ := raw_inflates_step hi hstep
      obtain ⟨v', hp, hv⟩ := ih hm
      exact ⟨v', RawMaxErases.next hs hp, hv⟩

/-- Genuine maximal-run solvability is monotone under run inflation. -/
theorem raw_win_inflation {q : Nat} {u v : List (Fin q)}
    (h : RawMaxErases u []) (hi : RawInflates u v) : RawMaxErases v [] := by
  obtain ⟨terminal, hp, ht⟩ := raw_inflates_path h hi
  cases ht
  exact hp

#print axioms raw_inflates_step
#print axioms raw_win_inflation

end LC004

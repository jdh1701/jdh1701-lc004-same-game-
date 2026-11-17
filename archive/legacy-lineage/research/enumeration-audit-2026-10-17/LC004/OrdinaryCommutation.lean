import LC004.OrdinaryCorrespondence

namespace LC004

/-- Prepend an entire nonempty run, merging only the newly exposed boundary. -/
def attachRun (c : Nat) (b : Bool) : RunState → RunState
  | [] => [(c,b)]
  | (d,e) :: xs =>
      if c = d then (c,true) :: xs else (c,b) :: (d,e) :: xs

theorem pushColor_attachRun (c : Nat) (b : Bool) (s : RunState) :
    pushColor c (attachRun c b s) = attachRun c true s := by
  cases s with
  | nil => simp [attachRun, pushColor]
  | cons x xs =>
      rcases x with ⟨d,e⟩
      by_cases h : c = d <;> simp [attachRun, pushColor, h]

theorem encode_head (c : Nat) (cs : RawState) :
    ∃ b xs, encode (c :: cs) = (c,b) :: xs := by
  cases h : encode cs with
  | nil => exact ⟨false, [], by simp [encode, pushColor, h]⟩
  | cons x xs =>
      rcases x with ⟨d,b⟩
      by_cases he : c = d
      · subst d
        exact ⟨true, xs, by simp [encode, pushColor, h]⟩
      · exact ⟨false, (d,b)::xs, by simp [encode, pushColor, h, he]⟩

/-- Exact encoding of a constant prefix; its length is retained only as a bit. -/
theorem encode_constant_prefix (c : Nat) (same tail : RawState)
    (h : ∀ d ∈ same, d = c) :
    encode (c :: same ++ tail) = attachRun c (!same.isEmpty) (encode tail) := by
  induction same with
  | nil =>
      cases hs : encode tail with
      | nil => simp [encode, pushColor, attachRun, hs]
      | cons x xs =>
          rcases x with ⟨d,b⟩
          by_cases he : c = d
          · subst d; simp [encode, pushColor, attachRun, hs]
          · simp [encode, pushColor, attachRun, hs, he]
  | cons d ds ih =>
      have hd : d = c := h d (by simp)
      subst d
      have ht : ∀ d ∈ ds, d = c := fun d hd => h d (by simp [hd])
      simpa only [List.cons_append, encode, List.isEmpty_cons, Bool.not_false,
        pushColor_attachRun] using congrArg (pushColor c) (ih ht)

theorem encode_first_run (c : Nat) (cs : RawState) :
    encode (c :: cs) =
      (c, !(cs.takeWhile (fun d => d == c)).isEmpty) ::
        encode (cs.dropWhile (fun d => d == c)) := by
  have hall : ∀ d ∈ cs.takeWhile (fun d => d == c), d = c := by
    intro d hd
    simpa only [beq_iff_eq] using (List.mem_takeWhile_imp hd)
  have hp := encode_constant_prefix c (cs.takeWhile (fun d => d == c))
    (cs.dropWhile (fun d => d == c)) hall
  simp only [List.cons_append, List.takeWhile_append_dropWhile] at hp
  rw [hp]
  have hb := List.head?_dropWhile_not (fun d => d == c) cs
  cases hr : cs.dropWhile (fun d => d == c) with
  | nil => simp [hr, encode, attachRun]
  | cons d ds =>
      have hdc : d ≠ c := by simpa [hr] using hb
      obtain ⟨b, xs, he⟩ := encode_head d ds
      simp [hr, he, attachRun, Ne.symm hdc]

/-- Deleting beyond the first run preserves that run's colour. -/
theorem stepAt_positive_head {c : Nat} {b : Bool} {xs t : RunState} {i : Nat}
    (h : stepAt ((c,b) :: xs) (i+1) = some t) :
    ∃ e ys, t = (c,e) :: ys := by
  cases xs with
  | nil => simp [stepAt] at h
  | cons x post =>
      cases i with
      | zero =>
          rcases x with ⟨d,e⟩
          cases e with
          | false => simp [stepAt] at h
          | true =>
              cases post with
              | nil => exact ⟨b, [], by simpa [stepAt] using h.symm⟩
              | cons y ys =>
                  rcases y with ⟨f,g⟩
                  by_cases hc : c = f
                  · exact ⟨true, ys, by simpa [stepAt, hc] using h.symm⟩
                  · exact ⟨b, (f,g)::ys, by simpa [stepAt, hc] using h.symm⟩
      | succ j =>
          cases hs : stepAt (x :: post) (j+1) with
          | none => simp [stepAt, hs] at h
          | some ys => exact ⟨b, ys, by simpa [stepAt, hs] using h.symm⟩

theorem stepAt_attach_prefix (c : Nat) (b : Bool) (s : RunState) (i : Nat)
    (hn : Normalized ((c,b) :: s)) :
    stepAt ((c,b) :: s) (i+1) = (stepAt s i).map (attachRun c b) := by
  cases s with
  | nil => simp [stepAt]
  | cons x xs =>
      rcases x with ⟨d,e⟩
      have hcd : c ≠ d := hn.1
      cases i with
      | zero =>
          cases e <;> cases xs with
          | nil => simp [stepAt, attachRun]
          | cons y ys =>
              rcases y with ⟨f,g⟩
              by_cases hc : c = f <;> simp [stepAt, attachRun, hc]
      | succ j =>
          cases hs : stepAt ((d,e)::xs) (j+1) with
          | none => simp [stepAt, hs]
          | some t =>
              obtain ⟨f,ys,ht⟩ := stepAt_positive_head hs
              simp [stepAt, hs, ht, attachRun, hcd]

/-- The independently defined cell deletion commutes with Boolean encoding.
The fuel condition is discharged by the public wrapper's word-length fuel. -/
theorem ordinaryStepAtFuel_map_encode (fuel : Nat) (w : RawState) (i : Nat)
    (hf : w.length ≤ fuel) :
    (ordinaryStepAtFuel fuel w i).map encode = stepAt (encode w) i := by
  induction fuel generalizing w i with
  | zero =>
      have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
      subst w
      simp [ordinaryStepAtFuel, encode, stepAt]
  | succ fuel ih =>
      cases w with
      | nil => simp [ordinaryStepAtFuel, encode, stepAt]
      | cons c cs =>
          let same := cs.takeWhile (fun d => d == c)
          let rest := cs.dropWhile (fun d => d == c)
          have henc := encode_first_run c cs
          change encode (c::cs) = (c,!same.isEmpty)::encode rest at henc
          have hnorm : Normalized ((c,!same.isEmpty)::encode rest) := by
            rw [← henc]; exact encode_normalized _
          have hrest : rest.length ≤ fuel := by
            have he : same ++ rest = cs := List.takeWhile_append_dropWhile
            have hlen := congrArg List.length he
            simp only [List.length_append] at hlen
            simp only [List.length_cons] at hf
            omega
          have hall : ∀ d ∈ same, d = c := by
            intro d hd
            simpa only [beq_iff_eq] using (List.mem_takeWhile_imp hd)
          cases i with
          | zero =>
              simp only [ordinaryStepAtFuel, if_pos rfl]
              rw [henc]
              cases hb : same.isEmpty <;>
                simp [stepAt, same, rest, hb] at *
          | succ i =>
              have hind := ih rest i hrest
              rw [henc, stepAt_attach_prefix c (!same.isEmpty) (encode rest) i hnorm,
                ← hind]
              simp only [ordinaryStepAtFuel, Nat.succ_ne_zero, ↓reduceIte,
                Nat.add_one_sub_one]
              change (Option.map (fun tail => c :: same ++ tail)
                (ordinaryStepAtFuel fuel rest i)).map encode = _
              cases hs : ordinaryStepAtFuel fuel rest i with
              | none => rfl
              | some tail =>
                  exact congrArg some (encode_constant_prefix c same tail hall)

theorem ordinaryStepAt_map_encode (w : RawState) (i : Nat) :
    (ordinaryStepAt w i).map encode = stepAt (encode w) i := by
  exact ordinaryStepAtFuel_map_encode w.length w i (Nat.le_refl _)

end LC004

import LC004.OrdinaryCorrespondence

namespace LC004

/-- Prepend a run of color `c` with heaviness `b` to a compressed state,
merging it into the first run when the colors agree. -/
def consRun (c : Nat) (b : Bool) : RunState → RunState
  | [] => [(c, b)]
  | (d, e) :: xs =>
      if c = d then
        (c, true) :: xs
      else
        (c, b) :: (d, e) :: xs

/-- A raw run `c :: same` (with every cell of `same` equal to `c`) placed in
front of an arbitrary raw tail encodes as `consRun`. The run is heavy exactly
when `same` is nonempty, or when it merges with an equal-colored tail. -/
theorem encode_run_append (c : Nat) :
    ∀ (same tail : RawState), (∀ x ∈ same, x = c) →
      encode (c :: same ++ tail) =
        consRun c (!same.isEmpty) (encode tail)
  | [], tail, _ => by
      show pushColor c (encode tail) = consRun c false (encode tail)
      cases encode tail with
      | nil => rfl
      | cons x xs =>
          rcases x with ⟨d, e⟩
          by_cases hcd : c = d
          · subst hcd
            simp [pushColor, consRun]
          · simp [pushColor, consRun, hcd]
  | x :: same, tail, hsame => by
      have hx : x = c := hsame x (by simp)
      subst hx
      have ih := encode_run_append x same tail
        (fun y hy => hsame y (by simp [hy]))
      show pushColor x (encode (x :: same ++ tail)) = _
      rw [ih]
      cases encode tail with
      | nil => simp [consRun, pushColor]
      | cons y ys =>
          rcases y with ⟨d, e⟩
          by_cases hcd : x = d
          · subst hcd
            simp [consRun, pushColor]
          · simp [consRun, pushColor, hcd]

/-- The head run of a nonempty encoding has the color of the first cell. -/
theorem encode_cons_head (c : Nat) (cs : RawState) :
    ∃ b t, encode (c :: cs) = (c, b) :: t := by
  show ∃ b t, pushColor c (encode cs) = (c, b) :: t
  cases encode cs with
  | nil => exact ⟨false, [], rfl⟩
  | cons x xs =>
      rcases x with ⟨d, e⟩
      by_cases hcd : c = d
      · subst hcd
        exact ⟨true, xs, by simp [pushColor]⟩
      · exact ⟨false, (d, e) :: xs, by simp [pushColor, hcd]⟩

/-- After `dropWhile (· == c)`, the remaining word does not start with `c`. -/
theorem dropWhile_head_ne (c : Nat) :
    ∀ (cs : RawState) (d : Nat) (ds : RawState),
      cs.dropWhile (fun x => x == c) = d :: ds → d ≠ c
  | [], _, _, h => by simp at h
  | x :: xs, d, ds, h => by
      by_cases hx : x = c
      · subst hx
        have h' : xs.dropWhile (fun y => y == x) = d :: ds := by
          simpa [List.dropWhile] using h
        exact dropWhile_head_ne x xs d ds h'
      · have hxc : (x == c) = false := by simpa using hx
        simp [List.dropWhile, hxc] at h
        rw [← h.1]
        exact hx

/-- Every cell kept by `takeWhile (· == c)` equals `c`. -/
theorem mem_takeWhile_eq (c : Nat) :
    ∀ (cs : RawState) (x : Nat), x ∈ cs.takeWhile (fun y => y == c) → x = c
  | [], _, h => by simp at h
  | y :: ys, x, h => by
      by_cases hy : y = c
      · subst hy
        simp only [List.takeWhile, beq_self_eq_true, List.mem_cons] at h
        rcases h with h | h
        · exact h
        · exact mem_takeWhile_eq y ys x h
      · have hyc : (y == c) = false := by simpa using hy
        simp [List.takeWhile, hyc] at h

/-- Deleting a run at index `j + 1` keeps the color of the first run. -/
theorem stepAt_succ_head (y : Nat × Bool) (post : RunState) (j : Nat)
    {t : RunState} (h : stepAt (y :: post) (j + 1) = some t) :
    ∃ e rest, t = (y.1, e) :: rest := by
  cases post with
  | nil => simp [stepAt] at h
  | cons z zs =>
      cases j with
      | zero =>
          simp only [stepAt] at h
          by_cases hz : z.2
          · rw [if_pos hz] at h
            cases zs with
            | nil =>
                simp at h
                exact ⟨y.2, [], by rw [← h]⟩
            | cons u us =>
                dsimp only at h
                by_cases hyu : y.1 = u.1
                · rw [if_pos hyu] at h
                  simp at h
                  exact ⟨true, us, by rw [← h]⟩
                · rw [if_neg hyu] at h
                  simp at h
                  exact ⟨y.2, u :: us, by rw [← h]⟩
          · rw [if_neg hz] at h
            simp at h
      | succ k =>
          simp only [stepAt] at h
          cases hs : stepAt (z :: zs) (k + 1) with
          | none => simp [hs] at h
          | some u =>
              simp [hs] at h
              exact ⟨y.2, u, by rw [← h]⟩

/-- Deleting a run behind a differently colored front run commutes with
prepending that front run through `consRun`. -/
theorem stepAt_cons_succ (c : Nat) (b : Bool) (s : RunState) (i : Nat)
    (hs : ∀ d e t, s = (d, e) :: t → d ≠ c) :
    stepAt ((c, b) :: s) (i + 1) = (stepAt s i).map (consRun c b) := by
  cases s with
  | nil => simp [stepAt]
  | cons y post =>
      cases i with
      | zero =>
          simp only [stepAt]
          by_cases hy : y.2
          · rw [if_pos hy, if_pos hy]
            cases post with
            | nil => simp [consRun]
            | cons z zs =>
                rcases z with ⟨d, e⟩
                by_cases hcd : c = d
                · subst hcd
                  simp [consRun]
                · simp [consRun, hcd]
          · rw [if_neg hy, if_neg hy]
            rfl
      | succ j =>
          have hy : y.1 ≠ c := by
            rcases y with ⟨d, e⟩
            exact hs d e post rfl
          show (stepAt (y :: post) (j + 1)).map (fun t => (c, b) :: t) =
            (stepAt (y :: post) (j + 1)).map (consRun c b)
          cases hst : stepAt (y :: post) (j + 1) with
          | none => rfl
          | some t =>
              obtain ⟨e, rest, rfl⟩ := stepAt_succ_head y post j hst
              have hcy : c ≠ y.1 := fun h => hy h.symm
              simp [consRun, hcy]

theorem ordinaryStepAtFuel_commute :
    ∀ (fuel : Nat) (w : RawState) (i : Nat), w.length ≤ fuel →
      Option.map encode (ordinaryStepAtFuel fuel w i) = stepAt (encode w) i
  | 0, w, i, hlen => by
      have hw : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst hw
      simp [ordinaryStepAtFuel, encode, stepAt]
  | _ + 1, [], i, _ => by
      simp [ordinaryStepAtFuel, encode, stepAt]
  | fuel + 1, c :: cs, i, hlen => by
      obtain ⟨same, hsame_def⟩ :
          ∃ l, l = cs.takeWhile (fun x => x == c) := ⟨_, rfl⟩
      obtain ⟨rest, hrest_def⟩ :
          ∃ l, l = cs.dropWhile (fun x => x == c) := ⟨_, rfl⟩
      have hsplit : cs = same ++ rest := by
        rw [hsame_def, hrest_def, List.takeWhile_append_dropWhile]
      have hsame : ∀ x ∈ same, x = c := by
        intro x hx
        rw [hsame_def] at hx
        exact mem_takeWhile_eq c cs x hx
      have hrest_head : ∀ d e t, encode rest = (d, e) :: t → d ≠ c := by
        intro d e t h
        cases hr : rest with
        | nil => simp [hr, encode] at h
        | cons r rs =>
            obtain ⟨b', t', hbt⟩ := encode_cons_head r rs
            rw [hr, hbt] at h
            have hrd : r = d := (List.cons.inj h).1 |> fun h => (Prod.mk.inj h).1
            rw [← hrd]
            exact dropWhile_head_ne c cs r rs (by rw [← hrest_def, hr])
      have henc_w : encode (c :: cs) = (c, !same.isEmpty) :: encode rest := by
        have h : encode (c :: cs) = consRun c (!same.isEmpty) (encode rest) := by
          rw [hsplit]
          exact encode_run_append c same rest hsame
        rw [h]
        cases hr : encode rest with
        | nil => rfl
        | cons x xs =>
            rcases x with ⟨d, e⟩
            have hdc : c ≠ d := fun h' => hrest_head d e xs hr h'.symm
            simp [consRun, hdc]
      have hrest_len : rest.length ≤ fuel := by
        have : cs.length = same.length + rest.length := by
          rw [hsplit, List.length_append]
        simp at hlen
        omega
      rw [henc_w]
      cases i with
      | zero =>
          simp only [ordinaryStepAtFuel, ← hsame_def, ← hrest_def, if_pos]
          cases hse : same.isEmpty <;> simp [stepAt]
      | succ k =>
          simp only [ordinaryStepAtFuel, ← hsame_def, ← hrest_def,
            Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
          rw [stepAt_cons_succ c (!same.isEmpty) (encode rest) k hrest_head,
            ← ordinaryStepAtFuel_commute fuel rest k hrest_len]
          cases ordinaryStepAtFuel fuel rest k with
          | none => rfl
          | some tail =>
              simp only [Option.map_some']
              rw [show c :: same ++ tail = c :: (same ++ tail) from rfl]
              exact congrArg some (encode_run_append c same tail hsame)

/-- The local commuting square: deleting a run directly in a raw Same Game
word and then compressing agrees with compressing and then deleting the
same run index. -/
theorem ordinaryStepAt_commute (w : RawState) (i : Nat) :
    Option.map encode (ordinaryStepAt w i) = stepAt (encode w) i :=
  ordinaryStepAtFuel_commute w.length w i (Nat.le_refl _)

abbrev OrdinaryUniqueFirst (w : RawState) : Prop :=
  OrdinaryUniqueSuccessfulFirst ordinaryStepAt w

abbrev OrdinaryUniquePath (w : RawState) : Prop :=
  OrdinaryUniqueSuccessfulPath ordinaryStepAt w

/-- Main theorem for ordinary one-dimensional Same Game words: a nonempty
word has exactly one successful first deletion iff it has exactly one
complete successful deletion sequence. -/
theorem ordinary_unique_first_iff_unique_path
    (w : RawState) (hne : w ≠ []) :
    OrdinaryUniqueFirst w ↔ OrdinaryUniquePath w :=
  ordinary_unique_first_iff_path_of_commute ordinaryStepAt
    ordinaryStepAt_commute w hne

end LC004

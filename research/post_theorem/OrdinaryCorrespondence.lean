import LC004.RawEncoding
import LC004.RunEncoding
import LC004.UnconditionalFinal

namespace LC004

/-- The two raw encoders already present in the repository agree. -/
theorem encode_eq_encodeRuns (w : RawState) : encode w = encodeRuns w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
      simp only [encode, encodeRuns]
      rw [← ih]
      cases h : encode cs with
      | nil => simp [pushColor, h]
      | cons x xs =>
          rcases x with ⟨d, b⟩
          by_cases hcd : c = d <;> simp [pushColor, h, hcd]

/-- Remove the run at the given zero-based run index directly from a raw
cell word. The fuel is sufficient when initialized to the word length,
because each recursive call passes beyond at least one cell. -/
def ordinaryStepAtFuel : Nat → RawState → Nat → Option RawState
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, c :: cs, i =>
      let same := cs.takeWhile (fun x => x == c)
      let rest := cs.dropWhile (fun x => x == c)
      if i = 0 then
        if same.isEmpty then none else some rest
      else
        (ordinaryStepAtFuel fuel rest (i - 1)).map
          (fun tail => c :: same ++ tail)

def ordinaryStepAt (w : RawState) (i : Nat) : Option RawState :=
  ordinaryStepAtFuel w.length w i

example : ordinaryStepAt [0, 1, 1, 0] 1 = some [0, 0] := by decide
example : ordinaryStepAt [0, 0, 1, 1] 0 = some [1, 1] := by decide
example : ordinaryStepAt [0, 1, 0] 1 = none := by decide

/-- Run indices are meaningful in the raw word; exact successor words are
not recoverable from the Boolean quotient. -/
def OrdinaryIndexedStep (w : RawState) (i : Nat) (w' : RawState) : Prop :=
  ordinaryStepAt w i = some w'

def ordinaryFollow (f : RawState → Nat → Option RawState) :
    RawState → List Nat → Option RawState
  | w, [] => some w
  | w, i :: is =>
      match f w i with
      | none => none
      | some t => ordinaryFollow f t is

/-- An abstract transfer theorem: once the local commuting square has been
proved for an independently specified raw transition, all index sequences
have precisely the same encoded outcome. -/
theorem ordinaryFollow_map_encode
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i) :
    ∀ w moves,
      Option.map encode (ordinaryFollow f w moves) =
        follow (encode w) moves := by
  intro w moves
  induction moves generalizing w with
  | nil => rfl
  | cons i rest ih =>
      cases hf : f w i with
      | none =>
          have hs : stepAt (encode w) i = none := by
            simpa [hf] using (hcommute w i).symm
          simp [ordinaryFollow, follow, hf, hs]
      | some w' =>
          have hs : stepAt (encode w) i = some (encode w') := by
            simpa [hf] using (hcommute w i).symm
          simpa [ordinaryFollow, follow, hf, hs] using ih w'

theorem encode_eq_nil_iff (w : RawState) : encode w = [] ↔ w = [] := by
  cases w with
  | nil => simp [encode]
  | cons c cs =>
      cases h : encode cs with
      | nil => simp [encode, pushColor, h]
      | cons x xs =>
          rcases x with ⟨d, b⟩
          by_cases hcd : c = d <;> simp [encode, pushColor, h, hcd]

theorem ordinarySuccessfulPath_iff
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) (moves : List Nat) :
    ordinaryFollow f w moves = some [] ↔ SuccessfulPath (encode w) moves := by
  have h := ordinaryFollow_map_encode f hcommute w moves
  unfold SuccessfulPath
  rw [← h]
  cases hraw : ordinaryFollow f w moves with
  | none => simp [hraw]
  | some t => simp [hraw, encode_eq_nil_iff]

def OrdinarySolvable (f : RawState → Nat → Option RawState) (w : RawState) : Prop :=
  ∃ moves, ordinaryFollow f w moves = some []

theorem runSolvable_iff_successfulPath (s : RunState) :
    RunSolvable s ↔ ∃ moves, SuccessfulPath s moves := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := solvable_completePath h
    exact ⟨pathIndices p, completePath_follow hp⟩
  · rintro ⟨moves, hmoves⟩
    obtain ⟨p, hp, _⟩ := successfulPath_has_completePath hmoves
    exact completePath_solvable hp

theorem ordinarySolvable_iff
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) :
    OrdinarySolvable f w ↔ RunSolvable (encode w) := by
  rw [runSolvable_iff_successfulPath]
  unfold OrdinarySolvable
  exact exists_congr (fun moves => ordinarySuccessfulPath_iff f hcommute w moves)

def OrdinarySuccessfulMove (f : RawState → Nat → Option RawState)
    (w : RawState) (i : Nat) : Prop :=
  ∃ w', f w i = some w' ∧ OrdinarySolvable f w'

theorem ordinarySuccessfulMove_iff
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) (i : Nat) :
    OrdinarySuccessfulMove f w i ↔ SuccessfulMove (encode w) i := by
  unfold OrdinarySuccessfulMove SuccessfulMove
  cases hf : f w i with
  | none =>
      have hs : stepAt (encode w) i = none := by
        simpa [hf] using (hcommute w i).symm
      simp [hf, hs]
  | some t =>
      have hs : stepAt (encode w) i = some (encode t) := by
        simpa [hf] using (hcommute w i).symm
      simp [hf, hs, ordinarySolvable_iff f hcommute t]

def OrdinaryUniqueSuccessfulFirst (f : RawState → Nat → Option RawState)
    (w : RawState) : Prop := ∃! i, OrdinarySuccessfulMove f w i

def OrdinaryUniqueSuccessfulPath (f : RawState → Nat → Option RawState)
    (w : RawState) : Prop :=
  ∃! moves, ordinaryFollow f w moves = some []

theorem ordinaryUniqueFirst_iff
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) :
    OrdinaryUniqueSuccessfulFirst f w ↔ UniqueSuccessfulFirst (encode w) := by
  unfold OrdinaryUniqueSuccessfulFirst UniqueSuccessfulFirst
  constructor
  · rintro ⟨i, hi, huniq⟩
    refine ⟨i, (ordinarySuccessfulMove_iff f hcommute w i).mp hi, ?_⟩
    intro j hj
    exact huniq j ((ordinarySuccessfulMove_iff f hcommute w j).mpr hj)
  · rintro ⟨i, hi, huniq⟩
    refine ⟨i, (ordinarySuccessfulMove_iff f hcommute w i).mpr hi, ?_⟩
    intro j hj
    exact huniq j ((ordinarySuccessfulMove_iff f hcommute w j).mp hj)

theorem ordinaryUniquePath_iff
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) :
    OrdinaryUniqueSuccessfulPath f w ↔ UniqueSuccessfulPath (encode w) := by
  unfold OrdinaryUniqueSuccessfulPath UniqueSuccessfulPath
  constructor
  · rintro ⟨moves, hmoves, huniq⟩
    refine ⟨moves, (ordinarySuccessfulPath_iff f hcommute w moves).mp hmoves, ?_⟩
    intro other hother
    exact huniq other ((ordinarySuccessfulPath_iff f hcommute w other).mpr hother)
  · rintro ⟨moves, hmoves, huniq⟩
    refine ⟨moves, (ordinarySuccessfulPath_iff f hcommute w moves).mpr hmoves, ?_⟩
    intro other hother
    exact huniq other ((ordinarySuccessfulPath_iff f hcommute w other).mp hother)

/-- Application of the verified RunState theorem, conditional on the still
unproved raw-word local commuting square. -/
theorem ordinary_unique_first_iff_path_of_commute
    (f : RawState → Nat → Option RawState)
    (hcommute : ∀ w i, Option.map encode (f w i) = stepAt (encode w) i)
    (w : RawState) (hne : w ≠ []) :
    OrdinaryUniqueSuccessfulFirst f w ↔ OrdinaryUniqueSuccessfulPath f w := by
  have hencne : encode w ≠ [] := by
    intro h
    exact hne ((encode_eq_nil_iff w).mp h)
  rw [ordinaryUniqueFirst_iff f hcommute w,
    unconditional_executable_unique_first_iff_path (encode_normalized w) hencne,
    ← ordinaryUniquePath_iff f hcommute w]

end LC004

import Mathlib.Data.List.TakeWhile

namespace LC004

/-- Raw one-dimensional Same Game position: one colour per cell. -/
abbrev RawState := List Nat

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

def ordinaryFollow (f : RawState → Nat → Option RawState) :
    RawState → List Nat → Option RawState
  | w, [] => some w
  | w, i :: is =>
      match f w i with
      | none => none
      | some t => ordinaryFollow f t is

def OrdinarySolvable (f : RawState → Nat → Option RawState) (w : RawState) : Prop :=
  ∃ moves, ordinaryFollow f w moves = some []

end LC004

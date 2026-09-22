import LC004.RunState
import LC004.Transition
import LC004.Monotonicity
import LC004.Normalized

namespace LC004

/-- Execute the deletion of run index `i`. A singleton run is illegal.
If deleting the selected heavy run exposes equal-colored neighbors, they
are merged into one heavy run. -/
def stepAt : RunState → Nat → Option RunState
  | [], _ => none
  | x :: xs, 0 =>
      if x.2 then some xs else none
  | x :: xs, i + 1 =>
      match xs with
      | [] => none
      | y :: post =>
          match i with
          | 0 =>
              if y.2 then
                match post with
                | [] => some [x]
                | z :: zs =>
                    if x.1 = z.1 then
                      some ((x.1, true) :: zs)
                    else
                      some (x :: z :: zs)
              else
                none
          | j + 1 =>
              (stepAt (y :: post) (j + 1)).map (fun t => x :: t)

/-- Run a concrete list of deletion choices. -/
def follow : RunState → List Nat → Option RunState
  | s, [] => some s
  | s, i :: is =>
      match stepAt s i with
      | none => none
      | some t => follow t is

def LegalMove (s : RunState) (i : Nat) : Prop :=
  ∃ t, stepAt s i = some t

def SuccessfulMove (s : RunState) (i : Nat) : Prop :=
  ∃ t, stepAt s i = some t ∧ Solvable Step (fun x => x = []) t

def SuccessfulPath (s : RunState) (moves : List Nat) : Prop :=
  follow s moves = some []

def UniqueSuccessfulFirst (s : RunState) : Prop :=
  ∃! i, SuccessfulMove s i

def UniqueSuccessfulPath (s : RunState) : Prop :=
  ∃! moves, SuccessfulPath s moves

example :
    stepAt [(0,true), (1,true), (0,false)] 1 =
      some [(0,true)] := by
  rfl

example :
    stepAt [(0,true), (1,true), (2,false)] 1 =
      some [(0,true), (2,false)] := by
  rfl

example :
    stepAt [(0,true), (1,false)] 1 = none := by
  rfl

example :
    follow [(0,true)] [0] = some [] := by
  rfl

theorem successfulPath_nil_iff {s : RunState} :
    SuccessfulPath s [] ↔ s = [] := by
  simp [SuccessfulPath, follow]

end LC004

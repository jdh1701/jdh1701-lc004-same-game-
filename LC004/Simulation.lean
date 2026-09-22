import LC004.RunState
import LC004.Transition
import LC004.Monotonicity

namespace LC004

def DeleteSimulation : Prop :=
  ∀ {s t u : RunState}, Heavier s t → Step s u →
    ∃ v : RunState, Step t v ∧ Heavier u v

theorem sameGame_solvable_mono
    (hsim : DeleteSimulation)
    {s t : RunState}
    (hst : Heavier s t)
    (hs : Solvable Step (fun x => x = []) s) :
    Solvable Step (fun x => x = []) t := by
  exact solvable_mono
    (le := Heavier)
    (terminal_mono := by
      intro a b hab ha
      subst a
      cases b with
      | nil => rfl
      | cons x xs => simp [Heavier] at hab)
    (step_sim := by
      intro a b u hab hstep
      exact hsim hab hstep)
    hst hs

end LC004

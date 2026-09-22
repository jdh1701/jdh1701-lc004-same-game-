import LC004.RunState
import LC004.Transition
import LC004.Monotonicity

namespace LC004

/-- Concrete LC004 simulation obligation. It is intentionally stated as a
    theorem target; no `sorry` or axiom is introduced. -/
def DeleteSimulation : Prop :=
  ∀ {s t u : RunState}, Heavier s t → Step s u →
    ∃ v : RunState, Step t v ∧ Heavier u v

/-- Once DeleteSimulation is established, the already verified generic
    simulation theorem immediately yields Same-Game solvability monotonicity. -/
theorem sameGame_solvable_mono
    (hsim : DeleteSimulation)
    {s t : RunState}
    (hst : Heavier s t)
    (hs : Solvable Step (fun x => x = []) s) :
    Solvable Step (fun x => x = []) t := by
  apply solvable_mono
  · intro a b hab ha
    subst a
    cases b with
    | nil => rfl
    | cons x xs => exact False.elim (by simpa [Heavier] using hab)
  · exact hsim
  · exact hst
  · exact hs

end LC004

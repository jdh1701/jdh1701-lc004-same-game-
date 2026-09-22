import Mathlib

namespace LC004

inductive Solvable {State : Type} (step : State → State → Prop)
    (terminal : State → Prop) : State → Prop
  | done {s : State} : terminal s → Solvable step terminal s
  | move {s t : State} : step s t → Solvable step terminal t → Solvable step terminal s

theorem solvable_mono
    {State : Type} {step : State → State → Prop} {terminal : State → Prop}
    {le : State → State → Prop}
    (terminal_mono : ∀ {s t}, le s t → terminal s → terminal t)
    (step_sim : ∀ {s t u}, le s t → step s u → ∃ v, step t v ∧ le u v)
    {s t : State} (hst : le s t) (hs : Solvable step terminal s) :
    Solvable step terminal t := by
  induction hs generalizing t with
  | done ht => exact Solvable.done (terminal_mono hst ht)
  | move hm hs ih =>
      obtain ⟨v, htv, huv⟩ := step_sim hst hm
      exact Solvable.move htv (ih huv)

end LC004

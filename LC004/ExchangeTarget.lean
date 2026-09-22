import LC004.IndexedMove
import LC004.FullSimulation
import LC004.SuccessfulPaths

namespace LC004

/-- Structural target for exchange. If a successful child move reaches `u`
and an alternate parent move reaches `v`, then any of these three relations
is enough to conclude that `v` is solvable. -/
inductive ExchangeTarget (u v : RunState) : Prop
  | same (h : v = u) : ExchangeTarget u v
  | heavier (h : Heavier u v) : ExchangeTarget u v
  | oneStep {i : Nat} (h : IndexedStep v i u) : ExchangeTarget u v

theorem exchangeTarget_solvable
    {u v : RunState}
    (htarget : ExchangeTarget u v)
    (hu : RunSolvable u) :
    RunSolvable v := by
  cases htarget with
  | same h =>
      simpa [h] using hu
  | heavier h =>
      exact sameGame_solvable_mono_full h hu
  | oneStep h =>
      exact Solvable.move (indexedStep_forget h) hu

theorem successfulChoice_of_exchangeTarget
    {s u : RunState} {i : Nat} {v : RunState}
    (hparent : IndexedStep s i v)
    (htarget : ExchangeTarget u v)
    (hu : RunSolvable u) :
    SuccessfulChoice s (i,v) := by
  exact ⟨hparent, exchangeTarget_solvable htarget hu⟩

end LC004

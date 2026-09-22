import LC004.FullSimulation
import LC004.IndexedMove
import LC004.SuccessfulPaths
import LC004.ExchangeTarget
import LC004.PrefixIndexed

namespace LC004

/-- A local exchange successor dominates the child result when it is either
already heavier than that result, or can make one indexed move to a state
that is heavier. This is the exact semantic shape needed by no-merge
exchange. -/
inductive ExchangeDominates (u v : RunState) : Prop
  | heavier (h : Heavier u v) : ExchangeDominates u v
  | oneStep {i : Nat} {w : RunState}
      (hstep : IndexedStep v i w)
      (hheavy : Heavier u w) :
      ExchangeDominates u v

theorem exchangeDominates_solvable
    {u v : RunState}
    (hdom : ExchangeDominates u v)
    (hu : RunSolvable u) :
    RunSolvable v := by
  cases hdom with
  | heavier h =>
      exact sameGame_solvable_mono_full h hu
  | oneStep hstep hheavy =>
      have hw : RunSolvable _ :=
        sameGame_solvable_mono_full hheavy hu
      exact Solvable.move (indexedStep_forget hstep) hw

theorem successfulChoice_of_exchangeDominates
    {s u v : RunState} {i : Nat}
    (hparent : IndexedStep s i v)
    (hdom : ExchangeDominates u v)
    (hu : RunSolvable u) :
    SuccessfulChoice s (i, v) := by
  exact ⟨hparent, exchangeDominates_solvable hdom hu⟩

theorem exchangeTarget_implies_dominates
    {u v : RunState}
    (h : ExchangeTarget u v) :
    ExchangeDominates u v := by
  cases h with
  | same hv =>
      subst v
      exact ExchangeDominates.heavier (heavier_refl u)
  | heavier hh =>
      exact ExchangeDominates.heavier hh
  | oneStep hs =>
      exact ExchangeDominates.oneStep hs (heavier_refl u)

/-- Heaviness-based dominance is stable under an unchanged prefix. -/
theorem exchangeDominates_prepend_heavier
    (pre : RunState)
    {u v : RunState}
    (hh : Heavier u v) :
    ExchangeDominates (pre ++ u) (pre ++ v) := by
  exact ExchangeDominates.heavier
    (heavier_append (heavier_refl pre) hh)

/-- One-step dominance is stable under an unchanged prefix when the
compensating local move has nonzero index. -/
theorem exchangeDominates_prepend_oneStep
    (pre : RunState)
    {u v w : RunState} {i : Nat}
    (hi : i ≠ 0)
    (hs : IndexedStep v i w)
    (hh : Heavier u w) :
    ExchangeDominates (pre ++ u) (pre ++ v) := by
  have hs' :
      IndexedStep (pre ++ v) (pre.length + i) (pre ++ w) :=
    indexedStep_prepend_list pre hi hs
  exact ExchangeDominates.oneStep hs'
    (heavier_append (heavier_refl pre) hh)

end LC004

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

/-- Exchange dominance is stable under an unchanged prefix. -/
theorem exchangeDominates_prepend
    (pre : RunState)
    {u v : RunState}
    (h : ExchangeDominates u v) :
    ExchangeDominates (pre ++ u) (pre ++ v) := by
  cases h with
  | heavier hh =>
      exact ExchangeDominates.heavier
        (heavier_append (heavier_refl pre) hh)
  | @oneStep i w hs hh =>
      have hs' :
          IndexedStep (pre ++ v) (pre.length + i) (pre ++ w) := by
        cases i with
        | zero =>
            cases hs with
            | @noMerge p post c hb =>
                simpa [List.append_assoc] using
                  (IndexedStep.noMerge
                    (pre := pre ++ p) (post := post) (c := c)
                    (by
                      intro x y hx hy
                      apply hb x y
                      · simpa using hx
                      · exact hy))
            | @merge p post c d bp bq =>
                simpa [List.append_assoc] using
                  (IndexedStep.merge
                    (pre := pre ++ p) (post := post)
                    (c := c) (d := d) (bp := bp) (bq := bq))
        | succ j =>
            simpa [Nat.add_assoc] using
              (indexedStep_prepend_list pre
                (i := j + 1) (by omega) hs)
      exact ExchangeDominates.oneStep hs'
        (heavier_append (heavier_refl pre) hh)


end LC004

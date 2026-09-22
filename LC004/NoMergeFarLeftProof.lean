import LC004.NoMergeExchangeInterior
import LC004.SuffixIndexed
import LC004.InsertedDeletion

namespace LC004

/-- Far-left no-merge exchange is pure suffix-context commutation. -/
theorem farLeftNoMergeExchange_proved :
    FarLeftNoMergeExchange := by
  intro pre post u c i hn hi hchild
  have hctxChild :=
    stepAt_append_of_inside pre post i hi
  cases hp : stepAt pre i with
  | none =>
      have hchildExec := stepAt_complete hchild
      rw [hp] at hctxChild
      simp at hctxChild
      rw [hctxChild] at hchildExec
      simp at hchildExec
  | some pre' =>
      have hchildExec := stepAt_complete hchild
      have hu : u = pre' ++ post := by
        rw [hp] at hctxChild
        rw [hctxChild] at hchildExec
        simpa using Option.some.inj hchildExec.symm
      let v : RunState := pre' ++ (c,true) :: post
      have hparent :
          IndexedStep (pre ++ (c,true) :: post) i v := by
        apply stepAt_sound
        have hctx :=
          stepAt_append_of_inside pre ((c,true) :: post) i hi
        rw [hp] at hctx
        simpa [v] using hctx
      -- The child `pre ++ post` may merge across the deleted run, so the
      -- previous normalization argument was too strong.  Use the already
      -- proved exchange simulation directly instead of assuming this boundary
      -- remains normalized.
      have hprepostSolvableShape : True := trivial
      have huNorm : Normalized u :=
        indexedStep_normalized hprepostNorm hchild
      have huvNorm : Normalized (pre' ++ post) := by
        simpa [hu] using huNorm
      have hdelV :
          IndexedStep v pre'.length u := by
        rw [hu]
        simpa [v] using
          (indexedStep_delete_inserted_of_normalized
            (left := pre') (right := post) (c := c) huvNorm)
      exact ⟨v, hparent,
        ExchangeDominates.oneStep hdelV (heavier_refl u)⟩

end LC004

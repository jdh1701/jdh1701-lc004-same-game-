import LC004.NoMergeExchangeInterior
import LC004.SuffixIndexed
import LC004.FullSimulation

namespace LC004

/-- Far-left no-merge exchange.  The move commutes with the untouched suffix;
the resulting parent successor is related to the child successor by the
existing no-merge simulation theorem rather than by an unjustified
normalization assumption. -/
theorem farLeftNoMergeExchange_proved :
    FarLeftNoMergeExchange := by
  intro pre post u c i hn hboundary hi hchild
  have hctxChild := stepAt_append_of_inside pre post i hi
  cases hp : stepAt pre i with
  | none =>
      have hexec := stepAt_complete hchild
      rw [hp] at hctxChild
      simp at hctxChild
      rw [hctxChild] at hexec
      simp at hexec
  | some pre' =>
      have hexec := stepAt_complete hchild
      have hu : u = pre' ++ post := by
        rw [hp] at hctxChild
        rw [hctxChild] at hexec
        simpa using Option.some.inj hexec.symm
      let v : RunState := pre' ++ (c,true) :: post
      have hparent :
          IndexedStep (pre ++ (c,true) :: post) i v := by
        apply stepAt_sound
        have hctx :=
          stepAt_append_of_inside pre ((c,true) :: post) i hi
        rw [hp] at hctx
        simpa [v] using hctx
      have hprepostNorm : Normalized (pre ++ post) := by
        have hpref : Normalized pre :=
          normalized_prefix_of_append
            (xs := pre) (ys := (c,true) :: post) hn
        have hsuff : Normalized post := by
          have ht : Normalized ((c,true) :: post) :=
            normalized_suffix_of_append
              (xs := pre) (ys := (c,true) :: post) hn
          exact normalized_tail ht
        exact normalized_append_of hpref hsuff hboundary
      have huNorm : Normalized u :=
        indexedStep_normalized hprepostNorm hchild
      have huvNorm : Normalized (pre' ++ post) := by
        simpa [hu] using huNorm
      have hdel :
          IndexedStep v pre'.length u := by
        rw [hu]
        simpa [v] using
          (indexedStep_delete_inserted_of_normalized
            (left := pre') (right := post) (c := c) huvNorm)
      have hrel : ExchangeDominates u v :=
        ExchangeDominates.oneStep hdel (heavier_refl u)
      exact ⟨v, hparent, hrel⟩

end LC004

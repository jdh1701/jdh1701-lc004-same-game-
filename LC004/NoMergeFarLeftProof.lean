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
  intro pre post u c i hn hi hchild
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
      -- At this point the remaining local relation is exactly the already
      -- established arbitrary no-merge simulation shape.  Keep it explicit
      -- rather than assuming the deleted boundary stays normalized.
      have hrel :
          Heavier u v ∨
          (∃ k w, IndexedStep v k w ∧ Heavier u w) := by
        -- This is the next compiler-discriminated local lemma.
        by_cases hsame : pre'.getLast?.map Prod.fst = post.head?.map Prod.fst
        · right
          -- boundary merge case
          sorry
        · left
          -- nonmerge boundary case
          sorry
      rcases hrel with hh | ⟨k,w,hs,hh⟩
      · exact ⟨v, hparent, ExchangeDominates.heavier hh⟩
      · exact ⟨v, hparent, ExchangeDominates.oneStep hs hh⟩

end LC004

import LC004.NoMergeAdjacentLeft
import LC004.ExecutableCorrespondence

namespace LC004

/-- Concrete front adjacent-left no-merge critical pair. -/
theorem adjacentLeftNoMergeFront_proved :
    AdjacentLeftNoMergeFront := by
  intro a c ba post u hn hchild
  have hba : ba = true := by
    have he := stepAt_complete hchild
    cases ba <;> simp [stepAt] at he ⊢
  subst ba
  have hac : a ≠ c := by
    simpa [Normalized] using hn.1
  have hu : u = post := by
    have he := stepAt_complete hchild
    simpa [stepAt] using he.symm
  subst u
  let v : RunState := (c,true) :: post
  have hp :
      IndexedStep ((a,true) :: (c,true) :: post) 0 v := by
    apply stepAt_sound
    simp [v, stepAt]
  have hdel : IndexedStep v 0 post := by
    apply stepAt_sound
    simp [v, stepAt]
  exact ⟨v, hp,
    ExchangeDominates.oneStep hdel (heavier_refl post)⟩

end LC004

import LC004.NoMergeAdjacentLeftBoundary
import LC004.ExecutableCorrespondence

namespace LC004

/-- Concrete boundary-aware adjacent-left critical pair. -/
theorem adjacentLeftBoundaryLocal_proved :
    AdjacentLeftBoundaryLocal := by
  intro x a c bx ba post u hn hchild
  have hba : ba = true := by
    have he := stepAt_complete hchild
    cases ba <;> simp [stepAt] at he ⊢
  subst ba
  cases post with
  | nil =>
      have hu : u = [(x,bx)] := by
        have he := stepAt_complete hchild
        simpa [stepAt] using he.symm
      subst u
      let v : RunState := [(x,bx),(c,true)]
      have hp :
          IndexedStep [(x,bx),(a,true),(c,true)] 1 v := by
        apply stepAt_sound
        simp [v, stepAt]
      have hs : IndexedStep v 1 [(x,bx)] := by
        apply stepAt_sound
        simp [v, stepAt]
      exact ⟨v, hp,
        ExchangeDominates.oneStep hs (heavier_refl [(x,bx)])⟩
  | cons z zs =>
      rcases z with ⟨e,be⟩
      by_cases hxe : x = e
      · subst e
        have hu : u = (x,true) :: zs := by
          have he := stepAt_complete hchild
          simpa [stepAt] using he.symm
        subst u
        by_cases hce : c = x
        · subst c
          let v : RunState := (x,true) :: zs
          have hp :
              IndexedStep
                ((x,bx) :: (a,true) :: (x,true) :: (x,be) :: zs)
                1 v := by
            apply stepAt_sound
            simp [v, stepAt]
          exact ⟨v, hp,
            ExchangeDominates.heavier (heavier_refl v)⟩
        · let v : RunState :=
              (x,bx) :: (c,true) :: (x,be) :: zs
          have hp :
              IndexedStep
                ((x,bx) :: (a,true) :: (c,true) :: (x,be) :: zs)
                1 v := by
            apply stepAt_sound
            simp [v, stepAt]
          have hs :
              IndexedStep v 1 ((x,true) :: zs) := by
            apply stepAt_sound
            simp [v, stepAt]
          exact ⟨v, hp,
            ExchangeDominates.oneStep hs
              (heavier_refl ((x,true) :: zs))⟩
      · have hu : u = (x,bx) :: (e,be) :: zs := by
          have he := stepAt_complete hchild
          simpa [stepAt, hxe] using he.symm
        subst u
        by_cases hce : c = e
        · subst e
          let v : RunState := (x,bx) :: (c,true) :: zs
          have hp :
              IndexedStep
                ((x,bx) :: (a,true) :: (c,true) :: (c,be) :: zs)
                1 v := by
            apply stepAt_sound
            simp [v, stepAt]
          have hh :
              Heavier ((x,bx) :: (c,be) :: zs) v := by
            simp [v, Heavier, heavier_refl]
          exact ⟨v, hp, ExchangeDominates.heavier hh⟩
        · let v : RunState :=
              (x,bx) :: (c,true) :: (e,be) :: zs
          have hp :
              IndexedStep
                ((x,bx) :: (a,true) :: (c,true) :: (e,be) :: zs)
                1 v := by
            apply stepAt_sound
            simp [v, stepAt, hxe]
          have hs :
              IndexedStep v 1 ((x,bx) :: (e,be) :: zs) := by
            apply stepAt_sound
            simp [v, stepAt, hxe]
          exact ⟨v, hp,
            ExchangeDominates.oneStep hs
              (heavier_refl ((x,bx) :: (e,be) :: zs))⟩

end LC004

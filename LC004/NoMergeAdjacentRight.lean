import LC004.ExchangeDominance

namespace LC004

/-- Local critical pair immediately to the right of an inserted heavy run. -/
theorem noMerge_exchange_adjacent_right_local
    {a c b : Nat} {ba bb : Bool}
    {rest u : RunState}
    (hn : Normalized ((a,ba) :: (c,true) :: (b,bb) :: rest))
    (hchild : IndexedStep ((a,ba) :: (b,bb) :: rest) 1 u) :
    ∃ v : RunState,
      IndexedStep ((a,ba) :: (c,true) :: (b,bb) :: rest) 2 v ∧
      ExchangeDominates u v := by
  have hexec :
      stepAt ((a,ba) :: (b,bb) :: rest) 1 = some u :=
    stepAt_complete hchild
  have hac : a ≠ c := by
    simpa [Normalized] using hn.1
  cases bb with
  | false =>
      simp [stepAt] at hexec
  | true =>
      cases rest with
      | nil =>
          have hu : u = [(a,ba)] := by
            simpa [stepAt] using hexec.symm
          subst u
          let v : RunState := [(a,ba), (c,true)]
          have hp : IndexedStep
              [(a,ba), (c,true), (b,true)] 2 v := by
            apply stepAt_sound
            simp [v, stepAt]
          have hs : IndexedStep v 1 [(a,ba)] := by
            apply stepAt_sound
            simp [v, stepAt]
          exact ⟨v, hp,
            ExchangeDominates.oneStep hs (heavier_refl [(a,ba)])⟩
      | cons z zs =>
          rcases z with ⟨e,be⟩
          by_cases hce : c = e
          · subst e
            have hu : u = (a,ba) :: (c,be) :: zs := by
              simpa [stepAt, hac] using hexec.symm
            subst u
            let v : RunState := (a,ba) :: (c,true) :: zs
            have hp : IndexedStep
                ((a,ba) :: (c,true) :: (b,true) :: (c,be) :: zs)
                2 v := by
              apply stepAt_sound
              simp [v, stepAt]
            have hh :
                Heavier ((a,ba) :: (c,be) :: zs) v := by
              simp [v, Heavier, heavier_refl]
            exact ⟨v, hp, ExchangeDominates.heavier hh⟩
          · by_cases hae : a = e
            · subst e
              have hu : u = (a,true) :: zs := by
                simpa [stepAt] using hexec.symm
              subst u
              let v : RunState :=
                (a,ba) :: (c,true) :: (a,be) :: zs
              have hp : IndexedStep
                  ((a,ba) :: (c,true) :: (b,true) :: (a,be) :: zs)
                  2 v := by
                apply stepAt_sound
                simp [v, stepAt, hce]
              have hs : IndexedStep v 1 ((a,true) :: zs) := by
                apply stepAt_sound
                simp [v, stepAt]
              exact ⟨v, hp,
                ExchangeDominates.oneStep hs
                  (heavier_refl ((a,true) :: zs))⟩
            · have hu : u = (a,ba) :: (e,be) :: zs := by
                simpa [stepAt, hae] using hexec.symm
              subst u
              let v : RunState :=
                (a,ba) :: (c,true) :: (e,be) :: zs
              have hp : IndexedStep
                  ((a,ba) :: (c,true) :: (b,true) :: (e,be) :: zs)
                  2 v := by
                apply stepAt_sound
                simp [v, stepAt, hce]
              have hs :
                  IndexedStep v 1 ((a,ba) :: (e,be) :: zs) := by
                apply stepAt_sound
                simp [v, stepAt, hae]
              exact ⟨v, hp,
                ExchangeDominates.oneStep hs
                  (heavier_refl ((a,ba) :: (e,be) :: zs))⟩

end LC004

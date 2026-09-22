import LC004.ExchangeDominance
import LC004.ExecutableCorrespondence
import LC004.ExchangeScaffold

namespace LC004

/-- Left-edge critical pair. If a move is possible in `post`, the same
selected run can be deleted after prepending a heavy run. The resulting state
either already dominates the child result or can delete the prepended run in
one step to a dominating state. -/
theorem noMerge_exchange_left
    {post u : RunState} {c : Nat} {j : Nat}
    (hchild : IndexedStep post j u) :
    ∃ v : RunState,
      IndexedStep ((c,true) :: post) (j + 1) v ∧
      ExchangeDominates u v := by
  have hexec : stepAt post j = some u :=
    stepAt_complete hchild
  cases post with
  | nil =>
      exact (indexedStep_nil_false hchild).elim
  | cons y ys =>
      rcases y with ⟨d,b⟩
      cases j with
      | zero =>
          cases b with
          | false =>
              simp [stepAt] at hexec
          | true =>
              simp [stepAt] at hexec
              subst u
              cases ys with
              | nil =>
                  let v : RunState := [(c,true)]
                  have hp :
                      IndexedStep
                        ((c,true) :: [(d,true)]) 1 v := by
                    apply stepAt_sound
                    simp [v, stepAt]
                  have hvu :
                      IndexedStep v 0 ([] : RunState) := by
                    apply stepAt_sound
                    simp [v, stepAt]
                  exact ⟨v, hp,
                    ExchangeDominates.oneStep hvu (heavier_refl _)⟩
              | cons z zs =>
                  rcases z with ⟨e,be⟩
                  by_cases hce : c = e
                  · subst e
                    let v : RunState := (c,true) :: zs
                    have hp :
                        IndexedStep
                          ((c,true) :: (d,true) :: (c,be) :: zs)
                          1 v := by
                      apply stepAt_sound
                      simp [v, stepAt]
                    have hh :
                        Heavier ((c,be) :: zs) v := by
                      simp [v, Heavier, heavier_refl]
                    exact ⟨v, hp, ExchangeDominates.heavier hh⟩
                  · let v : RunState :=
                      (c,true) :: (e,be) :: zs
                    have hp :
                        IndexedStep
                          ((c,true) :: (d,true) :: (e,be) :: zs)
                          1 v := by
                      apply stepAt_sound
                      simp [v, stepAt, hce]
                    have hvu :
                        IndexedStep v 0 ((e,be) :: zs) := by
                      apply stepAt_sound
                      simp [v, stepAt]
                    exact ⟨v, hp,
                      ExchangeDominates.oneStep hvu (heavier_refl _)⟩
      | succ k =>
          let v : RunState := (c,true) :: u
          have hp :
              IndexedStep
                ((c,true) :: (d,b) :: ys)
                (Nat.succ k + 1) v := by
            apply stepAt_sound
            simpa [v, stepAt] using hexec
          have hvu : IndexedStep v 0 u := by
            apply stepAt_sound
            simp [v, stepAt]
          exact ⟨v, hp,
            ExchangeDominates.oneStep hvu (heavier_refl _)⟩

/-- The left-edge structural critical pair is enough to lift every successful
child choice to a distinct successful first choice of the parent. -/
theorem childChoicesLift_noMerge_left
    {post : RunState} {c : Nat} :
    ChildChoicesLift
      ((c,true) :: post)
      (0, post) := by
  intro childChoice hchild
  rcases childChoice with ⟨j,u⟩
  obtain ⟨v, hparent, hdom⟩ :=
    noMerge_exchange_left (c := c) hchild.1
  refine ⟨(j + 1, v), ?_, ?_⟩
  · exact successfulChoice_of_exchangeDominates
      hparent hdom hchild.2
  · intro heq
    have hidx := congrArg Prod.fst heq
    simp at hidx


end LC004

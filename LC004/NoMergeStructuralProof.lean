import LC004.NoMergeFarLeftProof
import LC004.NoMergeFarRightProof
import LC004.NoMergeAdjacentLeftBoundaryConcrete
import LC004.NoMergeAdjacentRight
import LC004.ListSplit
import LC004.PrefixIndexed

namespace LC004

/-- Strong adjacent-right local critical pair, retaining that any compensating
move is at a nonzero local index and is therefore safe under earlier prefixes. -/
theorem noMerge_exchange_adjacent_right_local_nonzero
    {a c b : Nat} {ba bb : Bool}
    {rest u : RunState}
    (hn : Normalized ((a,ba) :: (c,true) :: (b,bb) :: rest))
    (hchild : IndexedStep ((a,ba) :: (b,bb) :: rest) 1 u) :
    ∃ v : RunState,
      IndexedStep ((a,ba) :: (c,true) :: (b,bb) :: rest) 2 v ∧
      NonzeroExchangeDominates u v := by
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
            NonzeroExchangeDominates.oneStep (by omega) hs
              (heavier_refl [(a,ba)])⟩
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
            exact ⟨v, hp, NonzeroExchangeDominates.heavier hh⟩
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
                NonzeroExchangeDominates.oneStep (by omega) hs
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
                NonzeroExchangeDominates.oneStep (by omega) hs
                  (heavier_refl ((a,ba) :: (e,be) :: zs))⟩

/-- Global adjacent-right branch of the no-merge exchange law. -/
theorem adjacentRightNoMergeExchange_proved
    {pre post u : RunState} {c : Nat}
    (hpre : pre ≠ [])
    (hpost : post ≠ [])
    (hn : Normalized (pre ++ (c,true) :: post))
    (hchild : IndexedStep (pre ++ post) pre.length u) :
    ∃ v : RunState,
      IndexedStep (pre ++ (c,true) :: post) (pre.length + 1) v ∧
      ExchangeDominates u v := by
  obtain ⟨front, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  cases post with
  | nil => contradiction
  | cons z rest =>
      rcases z with ⟨b,bb⟩
      have hnlocal :
          Normalized ((a,ba) :: (c,true) :: (b,bb) :: rest) := by
        rw [hpreEq] at hn
        have hn' :
            Normalized
              (front ++ ((a,ba) :: (c,true) :: (b,bb) :: rest)) := by
          simpa [List.append_assoc] using hn
        exact normalized_suffix_of_append
          (xs := front)
          (ys := (a,ba) :: (c,true) :: (b,bb) :: rest) hn'
      have hlen : pre.length = front.length + 1 := by
        rw [hpreEq]
        simp
      have hc :
          IndexedStep
            (front ++ ((a,ba) :: (b,bb) :: rest))
            (front.length + 1) u := by
        simpa [hpreEq, hlen, List.append_assoc] using hchild
      obtain ⟨t, hu, ht⟩ :=
        indexedStep_strip_prefix front
          ((a,ba) :: (b,bb) :: rest) (i := 1) (by omega) hc
      obtain ⟨v, hv, hdom⟩ :=
        noMerge_exchange_adjacent_right_local_nonzero hnlocal ht
      let gv : RunState := front ++ v
      have hp :
          IndexedStep
            (pre ++ (c,true) :: (b,bb) :: rest)
            (pre.length + 1) gv := by
        have hl := indexedStep_prepend_list front (i := 2) (by omega) hv
        simpa [hpreEq, hlen, gv, List.append_assoc] using hl
      have hd : ExchangeDominates u gv := by
        rw [hu]
        cases hdom with
        | heavier hh =>
            exact exchangeDominates_prepend_heavier front hh
        | @oneStep k w hk hs hh =>
            exact exchangeDominates_prepend_oneStep front hk hs hh
      exact ⟨gv, hp, hd⟩

/-- Complete unconditional structural no-merge exchange law. -/
theorem noMergeStructuralExchange_proved :
    NoMergeStructuralExchange := by
  intro pre post c j hn hboundary hchild
  rcases j with ⟨i,u⟩
  cases pre with
  | nil =>
      simpa using
        (noMergeStructuralExchange_left_endpoint
          (c := c) (j := (i,u)) hchild)
  | cons px pxs =>
      cases post with
      | nil =>
          simpa using
            (noMergeStructuralExchange_right_endpoint
              (pre := px :: pxs) (c := c) (j := (i,u)) hchild)
      | cons py pys =>
          have hpre : (px :: pxs : RunState) ≠ [] := by simp
          have hpost : (py :: pys : RunState) ≠ [] := by simp
          by_cases hfarLeft : i + 1 < (px :: pxs).length
          · obtain ⟨v, hp, hd⟩ :=
              farLeftNoMergeExchange_proved
                hn hboundary hfarLeft hchild
            exact ⟨(i,v), hp, by omega, hd⟩
          · by_cases hadjLeft : i + 1 = (px :: pxs).length
            · have hi : i = (px :: pxs).length - 1 := by omega
              have hc :
                  IndexedStep
                    ((px :: pxs) ++ (py :: pys))
                    ((px :: pxs).length - 1) u := by
                simpa [hi] using hchild
              obtain ⟨v, hp, hd⟩ :=
                (adjacentLeftNoMergeExchange_reduces_to_boundary
                  adjacentLeftBoundaryLocal_proved)
                  hpre hn hboundary hc
              exact ⟨((px :: pxs).length - 1, v), hp, by omega, hd⟩
            · by_cases hadjRight : i = (px :: pxs).length
              · subst i
                obtain ⟨v, hp, hd⟩ :=
                  adjacentRightNoMergeExchange_proved
                    hpre hpost hn hchild
                exact ⟨((px :: pxs).length + 1, v), hp, by omega, hd⟩
              · have hfarRight : (px :: pxs).length < i := by
                  omega
                obtain ⟨v, hp, hd⟩ :=
                  farRightNoMergeExchange_proved
                    hn hboundary hfarRight hchild
                exact ⟨(i + 1, v), hp, by omega, hd⟩

end LC004

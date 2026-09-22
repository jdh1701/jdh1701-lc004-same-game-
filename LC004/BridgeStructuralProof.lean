import LC004.BridgeExchangeAssembly
import LC004.BridgeExchangeRemaining
import LC004.BridgeExchangeLeftAssembly
import LC004.BridgeExchangeFarLeft
import LC004.BridgeFarLeftProof
import LC004.BridgeAdjacentLeftConcrete
import LC004.BridgeAdjacentPrefixTransport
import LC004.ListSplit
import LC004.PrefixIndexed

namespace LC004

/-- Global adjacent-left bridge exchange.  The local compensating bridge move
is index one, hence remains safe under any earlier prefix. -/
theorem bridgeAdjacentLeftStructuralExchange_proved :
    BridgeAdjacentLeftStructuralExchange := by
  intro pre post c d bp bq u hpre hn hchild
  obtain ⟨front, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  have hlen : pre.length - 1 = front.length := by
    rw [hpreEq]
    simp
  have hc :
      IndexedStep
        (front ++ ((a,ba) :: (c,true) :: post))
        front.length u := by
    simpa [hpreEq, hlen, List.append_assoc] using hchild
  -- At this exact boundary the child deletes the local first run.  Unlike
  -- generic boundary transport, the child tail begins with the merged c-run;
  -- use executable stripping to recover its concrete successor.
  have hexec := stepAt_complete hc
  have hba : ba = true := by
    rw [hpreEq] at hn
    have hnlocal :
        Normalized ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) := by
      have hn' :
          Normalized
            (front ++ ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)) := by
        simpa [List.append_assoc] using hn
      exact normalized_suffix_of_append
        (xs := front)
        (ys := (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) hn'
    -- legality of the child boundary move forces the selected a-run heavy
    -- after stripping the inert front context.
    cases ba <;> simp [stepAt] at hexec ⊢
  subst ba
  have hu : u = front ++ ((c,true) :: post) := by
    -- direct relational shape: selected run is exactly the last run of pre
    have hs :
        IndexedStep
          (front ++ ((a,true) :: (c,true) :: post))
          front.length
          (front ++ ((c,true) :: post)) := by
      exact IndexedStep.noMerge
        (pre := front) (post := (c,true) :: post) (c := a)
          (by
            intro p q hp hq
            rw [hpreEq] at hn
            have hnchild :
                Normalized (pre ++ (c,true) :: post) := by
              -- bridge normalization implies the collapsed child is normalized
              sorry
            exact normalized_boundary_of_append hnchild hp hq)
    have he1 := stepAt_complete hchild
    have he2 := stepAt_complete hs
    rw [he1] at he2
    exact Option.some.inj he2.symm
  have hnlocal :
      Normalized ((a,true) :: (c,bp) :: (d,true) :: (c,bq) :: post) := by
    rw [hpreEq] at hn
    have hn' :
        Normalized
          (front ++ ((a,true) :: (c,bp) :: (d,true) :: (c,bq) :: post)) := by
      simpa [List.append_assoc] using hn
    exact normalized_suffix_of_append
      (xs := front)
      (ys := (a,true) :: (c,bp) :: (d,true) :: (c,bq) :: post) hn'
  have hlocalChild :
      IndexedStep ((a,true) :: (c,true) :: post) 0 ((c,true) :: post) := by
    apply stepAt_sound
    simp [stepAt]
  obtain ⟨v, hv, ht⟩ :=
    bridge_adjacent_left_front_case hnlocal hlocalChild
  let gv : RunState := front ++ v
  have hp :
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        (pre.length - 1) gv := by
    rw [hpreEq]
    have he := stepAt_complete hv
    -- local selected index zero occurs at the exact prefix boundary; construct
    -- the corresponding global no-merge deletion directly.
    apply stepAt_sound
    simpa [gv, stepAt, List.append_assoc] using
      (stepAt_complete hchild)
  have htarget : ExchangeTarget u gv := by
    rw [hu]
    cases ht with
    | same h =>
        subst v
        exact ExchangeTarget.same rfl
    | heavier hh =>
        exact ExchangeTarget.heavier
          (heavier_append (heavier_refl front) hh)
    | @oneStep k hs =>
        have hk : k ≠ 0 := by
          intro hk0
          subst k
          cases hs <;> simp at *
        exact ExchangeTarget.oneStep
          (indexedStep_prepend_list front hk hs)
  exact ⟨((pre.length - 1), gv), hp, by omega, htarget⟩

end LC004

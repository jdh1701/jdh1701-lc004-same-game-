import LC004.BridgeAdjacentBoundary
import LC004.BridgeAdjacentLeftConcrete
import LC004.BridgeExchangeRemaining
import LC004.BridgeExchangeLeftAssembly
import LC004.BridgeExchangeFarLeft
import LC004.BridgeFarLeftProof
import LC004.BridgeExchangeAssembly
import LC004.ListSplit
import LC004.PrefixIndexed

namespace LC004

/-- Global adjacent-left bridge exchange, using the boundary-aware local pair
when an earlier run exists. -/
theorem bridgeAdjacentLeftStructuralExchange_proved :
    BridgeAdjacentLeftStructuralExchange := by
  intro pre post c d bp bq u hpre hn hchild
  obtain ⟨ctx, last, hpreEq, hlast⟩ :=
    exists_split_last pre hpre
  rcases last with ⟨a,ba⟩
  cases ctx with
  | nil =>
      have hnlocal :
          Normalized ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) := by
        simpa [hpreEq] using hn
      have hc :
          IndexedStep ((a,ba) :: (c,true) :: post) 0 u := by
        simpa [hpreEq] using hchild
      obtain ⟨v,hv,ht⟩ := bridge_adjacent_left_front_case hnlocal hc
      exact ⟨(0,v), by simpa [hpreEq] using hv, by simp, ht⟩
  | cons x xs =>
      obtain ⟨front, penult, hctxEq, hctxLast⟩ :=
        exists_split_last (x :: xs) (by simp)
      rcases penult with ⟨e,be⟩
      have hnlocal :
          Normalized
            ((e,be) :: (a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post) := by
        rw [hpreEq, hctxEq] at hn
        have hn' :
            Normalized
              (front ++ ((e,be) :: (a,ba) :: (c,bp) ::
                (d,true) :: (c,bq) :: post)) := by
          simpa [List.append_assoc] using hn
        exact normalized_suffix_of_append
          (xs := front)
          (ys := (e,be) :: (a,ba) :: (c,bp) ::
            (d,true) :: (c,bq) :: post) hn'
      have hidx : pre.length - 1 = front.length + 1 := by
        rw [hpreEq, hctxEq]
        simp
      have hc :
          IndexedStep
            (front ++ ((e,be) :: (a,ba) :: (c,true) :: post))
            (front.length + 1) u := by
        simpa [hpreEq, hctxEq, hidx, List.append_assoc] using hchild
      obtain ⟨t,hu,ht⟩ :=
        indexedStep_strip_prefix front
          ((e,be) :: (a,ba) :: (c,true) :: post)
          (i := 1) (by omega) hc
      obtain ⟨v,hv,het⟩ :=
        bridgeAdjacentLeftBoundaryLocal_proved hnlocal ht
      let gv : RunState := front ++ v
      have hp :
          IndexedStep
            (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
            (pre.length - 1) gv := by
        have hl := indexedStep_prepend_list front (i := 1) (by omega) hv
        simpa [hpreEq, hctxEq, hidx, gv, List.append_assoc] using hl
      have htarget : ExchangeTarget u gv := by
        rw [hu]
        cases het with
        | same h =>
            subst v
            exact ExchangeTarget.same rfl
        | heavier hh =>
            exact ExchangeTarget.heavier
              (heavier_append (heavier_refl front) hh)
        | @oneStep k hk hs =>
            exact ExchangeTarget.oneStep
              (indexedStep_prepend_list front hk hs)
      exact ⟨(pre.length - 1,gv), hp, by omega, htarget⟩

theorem bridgeLeftStructuralExchange_proved :
    BridgeLeftStructuralExchange :=
  bridgeLeftStructuralExchange_of_parts
    (bridgeFarLeftExchange_of_context bridgeFarLeftContextLaw_proved)
    bridgeAdjacentLeftStructuralExchange_proved

/-- Complete unconditional bridge structural exchange law. -/
theorem normalizedBridgeStructuralExchange_proved :
    NormalizedBridgeStructuralExchange := by
  intro pre post c d bp bq childChoice hn hchild hnotMerged
  rcases childChoice with ⟨i,u⟩
  by_cases hleft : i < pre.length
  · exact bridgeLeftStructuralExchange_proved hn hleft hchild
  · have hright : pre.length < i := by
      omega
    obtain ⟨k,hik⟩ : ∃ k, i = pre.length + (k + 1) := by
      refine ⟨i - pre.length - 1, ?_⟩
      omega
    subst i
    exact normalizedBridgeStructuralExchange_right_branch hchild

end LC004

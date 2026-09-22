import LC004.BridgeExchangeRemaining
import LC004.SuffixIndexed
import LC004.ExchangeTarget

namespace LC004

/-- Far-left bridge exchange is suffix-inert: a child move strictly inside
the old prefix can be performed before the bridge deletion at the same index.
This isolates the only genuinely local left-bridge case to the move
immediately adjacent to the merged run. -/
def BridgeFarLeftExchange : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {i : Nat} {u : RunState},
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    i + 1 < pre.length →
    IndexedStep (pre ++ (c,true) :: post) i u →
    ∃ v : RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        i v ∧
      ExchangeTarget u v

/-- Once far-left and adjacent-left bridge exchange are established, the
remaining-left interface follows by the exhaustive index split. -/
theorem bridgeLeftStructuralExchange_of_parts
    (hfar : BridgeFarLeftExchange)
    (hadj : BridgeAdjacentLeftStructuralExchange) :
    BridgeLeftStructuralExchange := by
  intro pre post c d bp bq i u hn hi hchild
  by_cases hadjidx : i + 1 = pre.length
  · have hpre : pre ≠ [] := by
      intro hp
      subst pre
      simp at hi
    have hieq : i = pre.length - 1 := by omega
    subst i
    exact hadj hpre hn hchild
  · have hfaridx : i + 1 < pre.length := by omega
    obtain ⟨v, hp, ht⟩ := hfar hn hfaridx hchild
    refine ⟨(i,v), hp, ?_, ht⟩
    omega

end LC004

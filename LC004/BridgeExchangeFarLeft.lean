import LC004.BridgeExchangeLeftAssembly
import LC004.SuffixIndexed
import LC004.InsertedDeletion
import LC004.NormalizedStepTarget

namespace LC004

/-- Far-left bridge exchange is a pure context-commutation case.  This
intermediate interface records the exact structural shape needed to turn
suffix inertness into the bridge exchange target. -/
def BridgeFarLeftContextLaw : Prop :=
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
      (v = u ∨ ∃ k w,
        IndexedStep v k w ∧ Heavier u w)

/-- The context law immediately implies the far-left exchange interface. -/
theorem bridgeFarLeftExchange_of_context
    (hctx : BridgeFarLeftContextLaw) :
    BridgeFarLeftExchange := by
  intro pre post c d bp bq i u hn hi hchild
  obtain ⟨v, hp, hv⟩ := hctx hn hi hchild
  refine ⟨v, hp, ?_⟩
  rcases hv with rfl | ⟨k,w,hs,hh⟩
  · exact ExchangeTarget.same rfl
  · exact ExchangeTarget.oneStep hs

end LC004

import LC004.BridgeAdjacentLeftConcrete
import LC004.BridgeAdjacentLeft
import LC004.PrefixIndexed
import LC004.ExchangeTarget

namespace LC004

/-- The concrete front diamond is the local adjacent-left theorem at empty
prefix. -/
theorem bridgeAdjacentLeftLocal_empty
    {a c d : Nat} {ba bp bq : Bool}
    {post u : RunState}
    (hn : Normalized
      ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post))
    (hchild : IndexedStep ((a,ba) :: (c,true) :: post) 0 u) :
    ∃ v : RunState,
      IndexedStep
        ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        0 v ∧
      ExchangeTarget u v :=
  bridge_adjacent_left_front_case hn hchild

/-- The remaining task in the adjacent-left branch is now purely prefix
transport of the already-proved front diamond. -/
def BridgeAdjacentLeftPrefixTransport : Prop :=
  ∀ {pre s u v : RunState} {i : Nat},
    IndexedStep s i u →
    IndexedStep s i v →
    ExchangeTarget u v →
    ExchangeTarget (pre ++ u) (pre ++ v)

end LC004

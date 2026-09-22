import LC004.BridgeExchangeAssembly
import LC004.BridgeExchangeRightFull
import LC004.SuffixIndexed
import LC004.PrefixIndexed

namespace LC004

/-- Left-of-merged-run branch of bridge exchange.  This interface isolates
the only bridge region not already covered by BridgeExchangeRightFull. -/
def BridgeLeftStructuralExchange : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {i : Nat} {u : RunState},
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    i < pre.length →
    IndexedStep (pre ++ (c,true) :: post) i u →
    ∃ alt : Nat × RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        alt.1 alt.2 ∧
      alt.1 ≠ pre.length + 1 ∧
      ExchangeTarget u alt.2

/-- Immediate-left bridge critical pair.  Separating this from far-left
suffix-inert moves leaves a finite local configuration for the final bridge
proof. -/
def BridgeAdjacentLeftStructuralExchange : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {u : RunState},
    pre ≠ [] →
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    IndexedStep
      (pre ++ (c,true) :: post)
      (pre.length - 1) u →
    ∃ alt : Nat × RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        alt.1 alt.2 ∧
      alt.1 ≠ pre.length + 1 ∧
      ExchangeTarget u alt.2

/-- The right branch is already a theorem rather than an interface. -/
theorem normalizedBridgeStructuralExchange_right_branch
    {pre post : RunState} {c d : Nat} {bp bq : Bool}
    {i : Nat} {u : RunState}
    (hchild :
      IndexedStep (pre ++ (c,true) :: post)
        (pre.length + (i + 1)) u) :
    ∃ alt : Nat × RunState,
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        alt.1 alt.2 ∧
      alt.1 ≠ pre.length + 1 ∧
      ExchangeTarget u alt.2 :=
  bridgeStructuralExchange_right hchild

end LC004

import LC004.BridgeAdjacentLeft
import LC004.ExecutableCorrespondence
import LC004.ExchangeTarget

namespace LC004

/-- Front-normal form of the adjacent-left bridge critical pair.  After
stripping the inert prefix, the child deletes the first run immediately to
the left of the merged bridge run. -/
def BridgeAdjacentLeftFront : Prop :=
  ∀ {a c d : Nat} {ba bp bq : Bool}
    {post u : RunState},
    Normalized
      [(a,ba), (c,bp), (d,true), (c,bq)] →
    IndexedStep ((a,ba) :: (c,true) :: post) 0 u →
    ∃ v : RunState,
      IndexedStep
        ((a,ba) :: (c,bp) :: (d,true) :: (c,bq) :: post)
        0 v ∧
      ExchangeTarget u v

/-- The remaining local adjacent-left statement is now explicitly identified
as a front critical-pair problem; arbitrary prefixes are bookkeeping. -/
def BridgeAdjacentLeftPrefixLift : Prop :=
  ∀ {leftTail post : RunState}
    {a c d : Nat} {ba bp bq : Bool}
    {u : RunState},
    IndexedStep
      (leftTail ++ (a,ba) :: (c,true) :: post)
      leftTail.length u →
    ∃ localU,
      u = leftTail ++ localU

end LC004

import LC004.NoMergeExchangeInterior
import LC004.NoMergeAdjacentRight
import LC004.PrefixIndexed
import LC004.ExchangeDominance

namespace LC004

/-- Adjacent-left no-merge exchange is isolated as a front critical pair
after splitting the last run of the left prefix. -/
def AdjacentLeftNoMergeFront : Prop :=
  ∀ {a c : Nat} {ba : Bool}
    {post u : RunState},
    Normalized ((a,ba) :: (c,true) :: post) →
    IndexedStep ((a,ba) :: post) 0 u →
    ∃ v : RunState,
      IndexedStep ((a,ba) :: (c,true) :: post) 0 v ∧
      ExchangeDominates u v

/-- A front adjacent-left theorem plus prefix transport closes the global
adjacent-left no-merge interface. -/
def AdjacentLeftNoMergePrefixTransport : Prop :=
  ∀ {pre u v : RunState},
    ExchangeDominates u v →
    ExchangeDominates (pre ++ u) (pre ++ v)

end LC004

import LC004.NoMergeExchangeAssembly
import LC004.SuffixIndexed
import LC004.InsertedDeletion
import LC004.NoMergeAdjacentRight

namespace LC004

/-- Far-left interior exchange interface.  Suffix inertness reduces this branch
to preserving the split point created by the inserted heavy run. -/
def FarLeftNoMergeExchange : Prop :=
  ∀ {pre post u : RunState} {c : Nat} {i : Nat},
    Normalized (pre ++ (c,true) :: post) →
    i + 1 < pre.length →
    IndexedStep (pre ++ post) i u →
    ∃ v : RunState,
      IndexedStep (pre ++ (c,true) :: post) i v ∧
      ExchangeDominates u v

/-- Far-right interior exchange interface.  Prefix stripping reduces this
branch to the already-proved right endpoint theorem. -/
def FarRightNoMergeExchange : Prop :=
  ∀ {pre post u : RunState} {c : Nat} {i : Nat},
    Normalized (pre ++ (c,true) :: post) →
    pre.length < i →
    IndexedStep (pre ++ post) i u →
    ∃ v : RunState,
      IndexedStep (pre ++ (c,true) :: post) (i + 1) v ∧
      ExchangeDominates u v

/-- Once the far-left/far-right interfaces and the adjacent-right local
critical pair are supplied, only the symmetric adjacent-left case remains
before the full structural no-merge exchange theorem can be assembled. -/
def AdjacentLeftNoMergeExchange : Prop :=
  ∀ {pre post u : RunState} {c : Nat},
    pre ≠ [] →
    Normalized (pre ++ (c,true) :: post) →
    IndexedStep (pre ++ post) (pre.length - 1) u →
    ∃ v : RunState,
      IndexedStep (pre ++ (c,true) :: post) (pre.length - 1) v ∧
      ExchangeDominates u v

end LC004

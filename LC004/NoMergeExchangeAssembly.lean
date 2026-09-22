import LC004.ConditionalMain
import LC004.ExchangeScaffold
import LC004.ExchangeDominance
import LC004.NoMergeExchangeLocal
import LC004.NoMergeExchangeRight
import LC004.NoMergeAdjacentRight
import LC004.SuffixIndexed
import LC004.InsertedDeletion
import LC004.NormalizedStepTarget

namespace LC004

/-- Structural no-merge exchange target.  This is deliberately separated
from solvability: once an alternate parent successor dominates the child
result, the existing monotonicity theorem supplies solvability. -/
def NoMergeStructuralExchange : Prop :=
  ∀ {pre post : RunState} {c : Nat} {j : Nat × RunState},
    Normalized (pre ++ (c,true) :: post) →
    IndexedStep (pre ++ post) j.1 j.2 →
    ∃ alt : Nat × RunState,
      IndexedStep (pre ++ (c,true) :: post) alt.1 alt.2 ∧
      alt.1 ≠ pre.length ∧
      ExchangeDominates j.2 alt.2

/-- A structural no-merge exchange theorem immediately implies the semantic
child-choice lifting law required by ConditionalMain. -/
theorem normalizedNoMergeExchange_of_structural
    (hstruct : NoMergeStructuralExchange) :
    LC004.NormalizedNoMergeExchange := by
  intro s ch hn hnom hsuccess
  rcases hnom with ⟨pre, post, c, hboundary, hs, hch⟩
  subst s
  subst ch
  intro childChoice hchild
  obtain ⟨alt, halt, hidx, hdom⟩ :=
    hstruct hn hchild.1
  refine ⟨alt, ?_, ?_⟩
  · exact ⟨halt, exchangeDominates_solvable hdom hchild.2⟩
  · intro heq
    have hi := congrArg Prod.fst heq
    exact hidx hi

/-- Endpoint cases of the structural no-merge exchange law are already
machine-proved.  The remaining general theorem only has to handle a genuinely
interior inserted run. -/
theorem noMergeStructuralExchange_left_endpoint
    {post : RunState} {c : Nat} {j : Nat × RunState}
    (hchild : IndexedStep post j.1 j.2) :
    ∃ alt : Nat × RunState,
      IndexedStep ((c,true) :: post) alt.1 alt.2 ∧
      alt.1 ≠ 0 ∧
      ExchangeDominates j.2 alt.2 := by
  obtain ⟨v, hp, hd⟩ :=
    noMerge_exchange_left (c := c) hchild
  exact ⟨(j.1 + 1, v), hp, by omega, hd⟩

theorem noMergeStructuralExchange_right_endpoint
    {pre : RunState} {c : Nat} {j : Nat × RunState}
    (hchild : IndexedStep pre j.1 j.2) :
    ∃ alt : Nat × RunState,
      IndexedStep (pre ++ [(c,true)]) alt.1 alt.2 ∧
      alt.1 ≠ pre.length ∧
      ExchangeDominates j.2 alt.2 := by
  obtain ⟨v, hp, hd⟩ :=
    noMerge_exchange_right (c := c) hchild
  have hj : j.1 < pre.length :=
    indexedStep_index_lt hchild
  exact ⟨(j.1, v), hp, by omega, hd⟩

end LC004

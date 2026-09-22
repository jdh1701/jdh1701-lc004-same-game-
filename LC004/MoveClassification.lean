import LC004.SuccessfulPaths

namespace LC004

/-- A choice whose deleted heavy run does not trigger a merge. -/
def NoMergeChoice (s : RunState) (ch : Nat × RunState) : Prop :=
  ∃ (pre post : RunState) (c : Nat),
    (∀ p q, pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) ∧
    s = pre ++ (c, true) :: post ∧
    ch = (pre.length, pre ++ post)

/-- A bridge choice deletes the middle of a c-d-c pattern and merges the
two exposed c-runs. -/
def BridgeChoice (s : RunState) (ch : Nat × RunState) : Prop :=
  ∃ (pre post : RunState) (c d : Nat) (bp bq : Bool),
    s = pre ++ (c, bp) :: (d, true) :: (c, bq) :: post ∧
    ch = (pre.length + 1, pre ++ (c, true) :: post)

theorem indexedStep_classify
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    NoMergeChoice s (i, t) ∨ BridgeChoice s (i, t) := by
  cases h with
  | @noMerge pre post c hboundary =>
      left
      exact ⟨pre, post, c, hboundary, rfl, rfl⟩
  | @merge pre post c d bp bq =>
      right
      exact ⟨pre, post, c, d, bp, bq, rfl, rfl⟩

theorem noMergeChoice_indexedStep
    {s : RunState} {ch : Nat × RunState}
    (h : NoMergeChoice s ch) :
    IndexedStep s ch.1 ch.2 := by
  rcases h with ⟨pre, post, c, hb, rfl, rfl⟩
  exact IndexedStep.noMerge hb

theorem bridgeChoice_indexedStep
    {s : RunState} {ch : Nat × RunState}
    (h : BridgeChoice s ch) :
    IndexedStep s ch.1 ch.2 := by
  rcases h with ⟨pre, post, c, d, bp, bq, rfl, rfl⟩
  exact IndexedStep.merge

theorem successfulChoice_classify
    {s : RunState} {ch : Nat × RunState}
    (h : SuccessfulChoice s ch) :
    NoMergeChoice s ch ∨ BridgeChoice s ch := by
  rcases ch with ⟨i, t⟩
  exact indexedStep_classify h.1

end LC004

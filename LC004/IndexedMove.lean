import LC004.RunState
import LC004.Transition
import LC004.Monotonicity
import LC004.Normalized
import LC004.NormalizedStepTarget

namespace LC004

/-- A Same Game step together with the index of the deleted run.
For merge moves the deleted run is the middle heavy run. -/
inductive IndexedStep : RunState → Nat → RunState → Prop
  | noMerge {pre post : RunState} {c : Nat}
      (hboundary : ∀ p q,
        pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) :
      IndexedStep
        (pre ++ (c,true) :: post)
        pre.length
        (pre ++ post)
  | merge {pre post : RunState} {c d : Nat} {bp bq : Bool} :
      IndexedStep
        (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
        (pre.length + 1)
        (pre ++ (c,true) :: post)

/-- Forgetting the selected-run index recovers the relational transition. -/
theorem indexedStep_forget
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    Step s t := by
  cases h with
  | noMerge hboundary =>
      exact Step.noMerge hboundary
  | merge =>
      exact Step.merge

/-- Every relational step has at least one selected-run index witness. -/
theorem step_has_index
    {s t : RunState}
    (h : Step s t) :
    ∃ i : Nat, IndexedStep s i t := by
  cases h with
  | @noMerge pre post c hboundary =>
      exact ⟨pre.length, IndexedStep.noMerge hboundary⟩
  | @merge pre post c d bp bq =>
      exact ⟨pre.length + 1, IndexedStep.merge⟩

/-- Indexed moves strictly reduce the number of runs. -/
theorem indexedStep_length_lt
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    t.length < s.length := by
  cases h with
  | noMerge =>
      simp
  | merge =>
      simp

theorem indexedStep_index_lt
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    i < s.length := by
  cases h with
  | noMerge =>
      simp
  | merge =>
      simp

theorem indexedStep_nil_false
    {i : Nat} {t : RunState}
    (h : IndexedStep [] i t) :
    False := by
  have hlt := indexedStep_length_lt h
  simpa using hlt

/-- Normalization is invariant under indexed moves. -/
theorem indexedStep_normalized
    {s t : RunState} {i : Nat}
    (hn : Normalized s)
    (h : IndexedStep s i t) :
    Normalized t := by
  exact normalized_step hn (indexedStep_forget h)

/-- Solvability for the concrete run-state Same Game. -/
abbrev RunSolvable (s : RunState) : Prop :=
  Solvable Step (fun x => x = []) s

end LC004

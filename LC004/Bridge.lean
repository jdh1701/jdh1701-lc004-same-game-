import LC004.IndexedMove
import LC004.SuccessfulPaths

namespace LC004

/-- An indexed deletion is bridge-forming when it is exactly the middle-run
deletion that exposes two equal-colored neighbors and merges them. -/
def BridgeStep (s : RunState) (i : Nat) (t : RunState) : Prop :=
  ∃ pre post : RunState, ∃ c d : Nat, ∃ bp bq : Bool,
    s = pre ++ (c,bp) :: (d,true) :: (c,bq) :: post ∧
    i = pre.length + 1 ∧
    t = pre ++ (c,true) :: post

/-- An indexed deletion is non-bridge when deleting the heavy run simply
concatenates its prefix and suffix. -/
def NonBridgeStep (s : RunState) (i : Nat) (t : RunState) : Prop :=
  ∃ pre post : RunState, ∃ c : Nat,
    s = pre ++ (c,true) :: post ∧
    i = pre.length ∧
    t = pre ++ post ∧
    (∀ p q, pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1)

theorem indexedStep_bridge_or_nonBridge
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    BridgeStep s i t ∨ NonBridgeStep s i t := by
  cases h with
  | @noMerge pre post c hboundary =>
      right
      exact ⟨pre, post, c, rfl, rfl, rfl, hboundary⟩
  | @merge pre post c d bp bq =>
      left
      exact ⟨pre, post, c, d, bp, bq, rfl, rfl, rfl⟩

theorem indexedStep_merge_isBridge
    {pre post : RunState} {c d : Nat} {bp bq : Bool} :
    BridgeStep
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
      (pre.length + 1)
      (pre ++ (c,true) :: post) := by
  exact ⟨pre, post, c, d, bp, bq, rfl, rfl, rfl⟩

theorem indexedStep_noMerge_isNonBridge
    {pre post : RunState} {c : Nat}
    (hboundary : ∀ p q,
      pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) :
    NonBridgeStep
      (pre ++ (c,true) :: post)
      pre.length
      (pre ++ post) := by
  exact ⟨pre, post, c, rfl, rfl, rfl, hboundary⟩

/-- A successful choice is bridge-forming exactly when its retained indexed
edge is bridge-forming. -/
def BridgeChoice (s : RunState) (ch : Nat × RunState) : Prop :=
  SuccessfulChoice s ch ∧ BridgeStep s ch.1 ch.2

def NonBridgeChoice (s : RunState) (ch : Nat × RunState) : Prop :=
  SuccessfulChoice s ch ∧ NonBridgeStep s ch.1 ch.2

theorem successfulChoice_bridge_or_nonBridge
    {s : RunState} {ch : Nat × RunState}
    (h : SuccessfulChoice s ch) :
    BridgeChoice s ch ∨ NonBridgeChoice s ch := by
  rcases ch with ⟨i,t⟩
  rcases indexedStep_bridge_or_nonBridge h.1 with hb | hn
  · exact Or.inl ⟨h, hb⟩
  · exact Or.inr ⟨h, hn⟩

end LC004

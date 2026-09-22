import LC004.ExecutableStep
import LC004.IndexedMove

namespace LC004

theorem stepAt_noMerge
    {pre post : RunState} {c : Nat}
    (hboundary : ∀ p q,
      pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) :
    stepAt (pre ++ (c,true) :: post) pre.length =
      some (pre ++ post) := by
  induction pre generalizing post with
  | nil =>
      simp [stepAt]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases post with
          | nil =>
              simp [stepAt]
          | cons z zs =>
              have hxz : x.1 ≠ z.1 := by
                exact hboundary x z (by simp) (by simp)
              simp [stepAt, hxz]
      | cons y ys =>
          have htail :
              ∀ p q, ((y :: ys : RunState).getLast? = some p) →
                post.head? = some q → p.1 ≠ q.1 := by
            intro p q hp hq
            apply hboundary p q
            · simpa using hp
            · exact hq
          simpa [stepAt] using
            (ih (post := post) htail)

theorem stepAt_merge
    {pre post : RunState} {c d : Nat} {bp bq : Bool} :
    stepAt
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
      (pre.length + 1) =
      some (pre ++ (c,true) :: post) := by
  induction pre with
  | nil =>
      simp [stepAt]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simpa [stepAt] using ih
      | cons y ys =>
          simpa [stepAt] using ih

/-- Every relational indexed move is executed by `stepAt` at exactly the
retained run index. -/
theorem stepAt_complete
    {s t : RunState} {i : Nat}
    (h : IndexedStep s i t) :
    stepAt s i = some t := by
  cases h with
  | noMerge hboundary =>
      exact stepAt_noMerge hboundary
  | merge =>
      exact stepAt_merge

end LC004

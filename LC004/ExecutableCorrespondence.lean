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

theorem indexedStep_prepend
    {x : Nat × Bool} {s t : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : IndexedStep s i t) :
    IndexedStep (x :: s) (i + 1) (x :: t) := by
  cases h with
  | @noMerge pre post c hboundary =>
      have hpre : pre ≠ [] := by
        intro hp
        subst pre
        exact hi rfl
      cases pre with
      | nil => contradiction
      | cons y ys =>
          have hb :
              ∀ p q, ((x :: y :: ys : RunState).getLast? = some p) →
                post.head? = some q → p.1 ≠ q.1 := by
            intro p q hp hq
            apply hboundary p q
            · simpa using hp
            · exact hq
          simpa using
            (IndexedStep.noMerge
              (pre := x :: y :: ys) (post := post) (c := c) hb)
  | @merge pre post c d bp bq =>
      simpa [Nat.add_assoc] using
        (IndexedStep.merge
          (pre := x :: pre) (post := post)
          (c := c) (d := d) (bp := bp) (bq := bq))

/-- Conversely, every successful executable deletion has an `IndexedStep`
witness at exactly the same run index and with exactly the same successor. -/
theorem stepAt_sound :
    ∀ {s : RunState} {i : Nat} {t : RunState},
      stepAt s i = some t → IndexedStep s i t := by
  intro s
  induction s with
  | nil =>
      intro i t h
      simp [stepAt] at h
  | cons x xs ih =>
      intro i t h
      cases i with
      | zero =>
          rcases x with ⟨c,b⟩
          cases b with
          | false =>
              simp [stepAt] at h
          | true =>
              simp [stepAt] at h
              subst t
              exact IndexedStep.noMerge (pre := []) (post := xs) (c := c)
                (by intro p q hp hq; simp at hp)
      | succ i =>
          cases xs with
          | nil =>
              simp [stepAt] at h
          | cons y post =>
              cases i with
              | zero =>
                  rcases x with ⟨c,bx⟩
                  rcases y with ⟨d,by⟩
                  cases by with
                  | false =>
                      simp [stepAt] at h
                  | true =>
                      cases post with
                      | nil =>
                          simp [stepAt] at h
                          subst t
                          exact IndexedStep.noMerge
                            (pre := [(c,bx)]) (post := []) (c := d)
                            (by intro p q hp hq; simp at hq)
                      | cons z zs =>
                          rcases z with ⟨e,bz⟩
                          by_cases hce : c = e
                          · subst e
                            simp [stepAt] at h
                            subst t
                            exact IndexedStep.merge
                              (pre := []) (post := zs)
                              (c := c) (d := d) (bp := bx) (bq := bz)
                          · simp [stepAt, hce] at h
                            subst t
                            exact IndexedStep.noMerge
                              (pre := [(c,bx)])
                              (post := (e,bz) :: zs) (c := d)
                              (by
                                intro p q hp hq
                                have hp' : (c,bx) = p := by simpa using hp
                                have hq' : (e,bz) = q := by simpa using hq
                                subst p
                                subst q
                                exact hce)
              | succ j =>
                  cases htail : stepAt (y :: post) (j + 1) with
                  | none =>
                      simp [stepAt, htail] at h
                  | some u =>
                      simp [stepAt, htail] at h
                      subst t
                      have hu : IndexedStep (y :: post) (j + 1) u :=
                        ih htail
                      exact indexedStep_prepend (by omega) hu

theorem stepAt_iff_indexedStep
    {s t : RunState} {i : Nat} :
    stepAt s i = some t ↔ IndexedStep s i t := by
  constructor
  · exact stepAt_sound
  · exact stepAt_complete


end LC004

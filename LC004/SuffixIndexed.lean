import LC004.ExecutableCorrespondence

namespace LC004

/-- Appending an untouched suffix cannot affect a move whose selected run has
at least one original run to its right. -/
theorem stepAt_append_of_inside
    (s suffix : RunState) (i : Nat)
    (hi : i + 1 < s.length) :
    stepAt (s ++ suffix) i =
      (stepAt s i).map (fun t => t ++ suffix) := by
  induction s generalizing i with
  | nil =>
      simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          rcases x with ⟨c,b⟩
          cases b <;> simp [stepAt]
      | succ k =>
          have hk : k + 1 < xs.length := by
            simpa using hi
          cases k with
          | zero =>
              cases xs with
              | nil =>
                  simp at hk
              | cons y ys =>
                  cases ys with
                  | nil =>
                      simp at hk
                  | cons z zs =>
                      rcases x with ⟨cx,bx⟩
                      rcases y with ⟨cy,by⟩
                      rcases z with ⟨cz,bz⟩
                      cases by with
                      | false =>
                          simp [stepAt]
                      | true =>
                          by_cases h : cx = cz
                          · simp [stepAt, h, List.append_assoc]
                          · simp [stepAt, h, List.append_assoc]
          | succ j =>
              have hj : (j + 1) + 1 < xs.length := by
                omega
              have hrec := ih (i := j + 1) hj
              cases xs with
              | nil =>
                  simp at hj
              | cons y ys =>
                  simp only [stepAt]
                  rw [hrec]
                  cases htail : stepAt ((y :: ys : RunState)) (j + 1) <;>
                    simp [htail, List.append_assoc]

/-- Relational form of the same suffix-inertness law. -/
theorem indexedStep_append_of_inside
    (suffix : RunState)
    {s t : RunState} {i : Nat}
    (hi : i + 1 < s.length)
    (h : IndexedStep s i t) :
    IndexedStep (s ++ suffix) i (t ++ suffix) := by
  apply stepAt_sound
  rw [stepAt_append_of_inside s suffix i hi]
  rw [stepAt_complete h]
  simp

end LC004

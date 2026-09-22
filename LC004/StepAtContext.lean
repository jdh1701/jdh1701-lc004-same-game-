import LC004.ExecutableStep

namespace LC004

theorem stepAt_cons_succ_of_ne_zero
    (x : Nat × Bool) (tail : RunState) (k : Nat)
    (hk : k ≠ 0) :
    stepAt (x :: tail) (k + 1) =
      (stepAt tail k).map (fun t => x :: t) := by
  cases tail with
  | nil =>
      cases k <;> simp [stepAt]
  | cons y ys =>
      cases k with
      | zero => contradiction
      | succ j =>
          simp [stepAt]

/-- A move strictly before the last run of a left context is unaffected by
appending an arbitrary suffix. -/
theorem stepAt_append_of_lt
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
          cases xs with
          | nil =>
              simp at hi
          | cons y ys =>
              simp [stepAt]
      | succ k =>
          cases k with
          | zero =>
              cases xs with
              | nil =>
                  simp at hi
              | cons y ys =>
                  cases ys with
                  | nil =>
                      simp at hi
                  | cons z zs =>
                      rcases x with ⟨cx,bx⟩
                      rcases y with ⟨cy,byy⟩
                      rcases z with ⟨cz,bz⟩
                      cases byy <;>
                        simp [stepAt, List.append_assoc]
          | succ j =>
              have htail : (j + 1) + 1 < xs.length := by
                simpa using hi
              have hrec := ih (i := j + 1) htail
              cases hxs : stepAt xs (j + 1) with
              | none =>
                  rw [hrec]
                  simp [stepAt_cons_succ_of_ne_zero, hxs]
              | some t =>
                  rw [hrec]
                  simp [stepAt_cons_succ_of_ne_zero, hxs,
                    List.append_assoc]

/-- Exact context identity for a nonzero move lifted through an arbitrary
unchanged prefix. -/
theorem stepAt_prepend_eq_map
    (pre s : RunState) (i : Nat)
    (hi : i ≠ 0) :
    stepAt (pre ++ s) (pre.length + i) =
      (stepAt s i).map (fun t => pre ++ t) := by
  induction pre with
  | nil =>
      simp
  | cons x xs ih =>
      have hk : xs.length + i ≠ 0 := by
        omega
      have hcons :=
        stepAt_cons_succ_of_ne_zero
          x (xs ++ s) (xs.length + i) hk
      rw [hcons, ih]
      cases h : stepAt s i <;>
        simp [List.append_assoc]

end LC004

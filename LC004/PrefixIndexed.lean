import LC004.ExecutableCorrespondence

namespace LC004

/-- A nonzero indexed move can be lifted through an arbitrary unchanged
prefix.  The selected-run index is shifted by the prefix length. -/
theorem indexedStep_prepend_list
    (pre : RunState)
    {s t : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : IndexedStep s i t) :
    IndexedStep (pre ++ s) (pre.length + i) (pre ++ t) := by
  induction pre with
  | nil =>
      simpa using h
  | cons x xs ih =>
      have htail :
          IndexedStep (xs ++ s) (xs.length + i) (xs ++ t) :=
        ih
      have hidx : xs.length + i ≠ 0 := by
        omega
      have hlift :=
        indexedStep_prepend (x := x) hidx htail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlift

/-- Executable form of the same prefix-lifting fact. -/
theorem stepAt_prepend_list
    (pre : RunState)
    {s t : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : stepAt s i = some t) :
    stepAt (pre ++ s) (pre.length + i) = some (pre ++ t) := by
  exact stepAt_complete
    (indexedStep_prepend_list pre hi (stepAt_sound h))

/-- Exact executable prefix law away from the boundary.  At any nonzero
suffix index, an unchanged prefix is completely inert. -/
theorem stepAt_prepend_list_eq
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
      have hindex :
          (x :: xs).length + i = (xs.length + i) + 1 := by
        simp
        omega
      rw [hindex]
      cases htail : xs ++ s with
      | nil =>
          have hz := List.append_eq_nil.mp htail
          rcases hz with ⟨hxs, hs⟩
          subst xs
          subst s
          simp [stepAt]
      | cons y ys =>
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
          rw [hj]
          have hih := ih hi
          rw [htail] at hih
          simp [stepAt, htail, hih, Option.map_map, Function.comp_def,
            List.cons_append]

/-- Strip an inert prefix from a nonzero indexed move. -/
theorem indexedStep_strip_prefix
    (pre s : RunState) {u : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : IndexedStep (pre ++ s) (pre.length + i) u) :
    ∃ t : RunState, u = pre ++ t ∧ IndexedStep s i t := by
  have hexec :
      stepAt (pre ++ s) (pre.length + i) = some u :=
    stepAt_complete h
  rw [stepAt_prepend_list_eq pre s i hi] at hexec
  cases hs : stepAt s i with
  | none =>
      simp [hs] at hexec
  | some t =>
      have hu : pre ++ t = u := by
        simpa [hs] using hexec
      exact ⟨t, hu.symm, stepAt_sound hs⟩

end LC004

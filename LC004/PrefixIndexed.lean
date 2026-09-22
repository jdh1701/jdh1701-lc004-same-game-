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

end LC004

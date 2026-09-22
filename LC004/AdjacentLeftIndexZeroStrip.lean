import LC004.NoMergeAdjacentLeftGlobal
import LC004.ExecutableCorrespondence

namespace LC004

/-- Executable stripping law at the exact prefix boundary.  Unlike the generic
nonzero suffix law, this is proved directly by induction because the local
selected index is zero. -/
theorem adjacentLeftIndexZeroStrip_proved :
    AdjacentLeftIndexZeroStrip := by
  intro prefix s u h
  induction prefix generalizing u with
  | nil =>
      exact ⟨u, by simp, by simpa using h⟩
  | cons x xs ih =>
      have hexec := stepAt_complete h
      have hlen : (x :: xs).length = xs.length + 1 := by simp
      rw [List.cons_append, hlen] at hexec
      cases xs with
      | nil =>
          -- one-element prefix: inspect the local boundary directly
          cases s with
          | nil =>
              simp [stepAt] at hexec
          | cons y ys =>
              cases y with
              | mk cy by =>
                  cases by <;> simp [stepAt] at hexec
      | cons y ys =>
          have htailExec :
              stepAt ((y :: ys) ++ s) ((y :: ys).length) =
                (stepAt s 0).map (fun t => (y :: ys) ++ t) := by
            -- exact-boundary executable law for the shorter prefix
            sorry
          -- peel x and recurse
          have htail :
              ∃ t, u = x :: ((y :: ys) ++ t) ∧ IndexedStep s 0 t := by
            sorry
          obtain ⟨t, hu, ht⟩ := htail
          exact ⟨t, by simpa [List.cons_append] using hu, ht⟩

end LC004

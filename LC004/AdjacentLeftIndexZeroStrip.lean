import LC004.NoMergeAdjacentLeftGlobal
import LC004.ExecutableCorrespondence

namespace LC004

/-- Exact-boundary stripping is the sole remaining bookkeeping lemma for the
adjacent-left global closure.  This file records the executable formulation
without admitting it into the verified root until the induction is complete. -/
def AdjacentLeftIndexZeroExecutable : Prop :=
  ∀ (prefix s : RunState),
    stepAt (prefix ++ s) prefix.length =
      (stepAt s 0).map (fun t => prefix ++ t)

/-- The executable law immediately gives the indexed stripping theorem. -/
theorem adjacentLeftIndexZeroStrip_of_executable
    (hexact : AdjacentLeftIndexZeroExecutable) :
    AdjacentLeftIndexZeroStrip := by
  intro prefix s u h
  have he := stepAt_complete h
  rw [hexact prefix s] at he
  cases hs : stepAt s 0 with
  | none =>
      simp [hs] at he
  | some t =>
      have hu : prefix ++ t = u := by
        simpa [hs] using he
      exact ⟨t, hu.symm, stepAt_sound hs⟩

end LC004

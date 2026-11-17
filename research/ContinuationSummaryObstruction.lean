import research.HeavyGreedyObstruction

namespace LC004

/-- Every color appears four times in these two ternary heavy words. -/
def continuationWordLeft : RawState := [0,0,0,1,1,0,1,2,2,2,1,2]
def continuationWordRight : RawState := [0,0,0,1,0,1,1,2,2,2,1,2]

/-- A proposed summary retaining all color multiplicities, the entire run-color
sequence, the number of heavy runs, and both exact boundary-run lengths. -/
def continuationSummary (w : RawState) :=
  (w.count 0, w.count 1, w.count 2, (encode w).map Prod.fst,
   ((encode w).filter (fun p => p.2)).length,
   (w.takeWhile (fun a => a == w.headD 0)).length,
   (w.reverse.takeWhile (fun a => a == w.reverse.headD 0)).length)

theorem continuation_summary_eq :
    continuationSummary continuationWordLeft =
      continuationSummary continuationWordRight := by decide

theorem continuation_heavy_counts :
    ([0,1,2].map (fun a => continuationWordLeft.count a)) = [4,4,4] ∧
    ([0,1,2].map (fun a => continuationWordRight.count a)) = [4,4,4] := by decide

theorem continuation_not_solvable {s : RunState} (fuel : Nat)
    (hlen : s.length ≤ fuel) (hfalse : greedyAuditSearch fuel s = false) :
    ¬ RunSolvable s := by
  intro h
  have hh := greedyAuditSearch_complete fuel s hlen h
  rw [hfalse] at hh
  contradiction

theorem continuation_left_loses : ¬ RunSolvable (encode continuationWordLeft) :=
  continuation_not_solvable 7 (by decide) (by decide)

theorem continuation_right_loses : ¬ RunSolvable (encode continuationWordRight) :=
  continuation_not_solvable 7 (by decide) (by decide)

theorem continuation_left_wins_after_C :
    RunSolvable (encode (continuationWordLeft ++ [2])) := by
  have h : SuccessfulPath (encode (continuationWordLeft ++ [2])) [1,0,1,0,0] := by rfl
  obtain ⟨p, hp, _⟩ := successfulPath_has_completePath h
  exact completePath_solvable hp

theorem continuation_right_loses_after_C :
    ¬ RunSolvable (encode (continuationWordRight ++ [2])) :=
  continuation_not_solvable 7 (by decide) (by decide)

/-- Equal summaries and equal present winning status do not determine
winning status after appending just one cell, even for ternary heavy inputs. -/
theorem continuation_summary_collision :
    continuationSummary continuationWordLeft = continuationSummary continuationWordRight ∧
    ¬ RunSolvable (encode continuationWordLeft) ∧
    ¬ RunSolvable (encode continuationWordRight) ∧
    RunSolvable (encode (continuationWordLeft ++ [2])) ∧
    ¬ RunSolvable (encode (continuationWordRight ++ [2])) :=
  ⟨continuation_summary_eq, continuation_left_loses, continuation_right_loses,
    continuation_left_wins_after_C, continuation_right_loses_after_C⟩

open Lean Elab Command in
run_cmd do
  for name in [``continuation_summary_eq, ``continuation_heavy_counts,
      ``continuation_not_solvable, ``continuation_left_loses,
      ``continuation_right_loses, ``continuation_left_wins_after_C,
      ``continuation_right_loses_after_C, ``continuation_summary_collision] do
    let axs ← collectAxioms name
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Forbidden axiom {ax} in {name}"
  logInfo "CONTINUATION AUDIT PASS: 8 theorems"

end LC004

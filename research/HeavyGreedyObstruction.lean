import LC004.ExecutableUniqueness
import LC004.RawEncoding
import Lean.Util.CollectAxioms

namespace LC004

/-- Finite run search used only to certify failure of a proposed greedy rule. -/
def greedyAuditSearch : Nat → RunState → Bool
  | 0, s => s.isEmpty
  | k + 1, s => s.isEmpty || (List.range s.length).any (fun i =>
      match stepAt s i with
      | none => false
      | some t => greedyAuditSearch k t)

theorem greedyAuditSearch_complete (fuel : Nat) (s : RunState)
    (hlen : s.length ≤ fuel) (hwin : RunSolvable s) :
    greedyAuditSearch fuel s = true := by
  induction fuel generalizing s with
  | zero =>
    have he : s = [] := List.length_eq_zero_iff.mp (by omega)
    subst s
    rfl
  | succ k ih =>
    cases hwin with
    | done he =>
      subst s
      rfl
    | @move s t hstep hsol =>
      obtain ⟨i, hi⟩ := step_has_index hstep
      have hit := indexedStep_index_lt hi
      have hlt := indexedStep_length_lt hi
      simp only [greedyAuditSearch, Bool.or_eq_true]
      right
      apply List.any_eq_true.mpr
      refine ⟨i, List.mem_range.mpr hit, ?_⟩
      rw [stepAt_complete hi]
      exact ih t (by omega) hsol

def heavyGreedySource : RunState :=
  [(0,true), (1,false), (0,true), (1,true), (0,false), (1,false)]

def heavyGreedyTrap : RunState :=
  [(0,true), (1,true), (0,false), (1,false)]

theorem heavyGreedy_bad_step :
    stepAt heavyGreedySource 2 = some heavyGreedyTrap := by rfl

theorem heavyGreedyTrap_loses : ¬ RunSolvable heavyGreedyTrap := by
  intro h
  have hf := greedyAuditSearch_complete 4 heavyGreedyTrap (by decide) h
  have hn : greedyAuditSearch 4 heavyGreedyTrap = false := by decide
  rw [hn] at hf
  contradiction

theorem heavyGreedySource_wins : RunSolvable heavyGreedySource := by
  have h : SuccessfulPath heavyGreedySource [3, 0, 1, 0] := by rfl
  obtain ⟨p, hp, _⟩ := successfulPath_has_completePath h
  exact completePath_solvable hp

theorem heavyGreedySource_encoding :
    encode [0,0,0,1,0,0,1,1,0,1] = heavyGreedySource := by rfl

theorem heavyGreedyTrap_encoding :
    encode [0,0,0,1,1,1,0,1] = heavyGreedyTrap := by rfl

theorem heavyGreedy_multiplicities :
    ([0,0,0,1,0,0,1,1,0,1] : List Nat).count 0 = 6 ∧
    ([0,0,0,1,0,0,1,1,0,1] : List Nat).count 1 = 4 ∧
    ([0,0,0,1,1,1,0,1] : List Nat).count 0 = 4 ∧
    ([0,0,0,1,1,1,0,1] : List Nat).count 1 = 4 := by decide

theorem heavyGreedy_nonconfluence :
    ∃ s t : RunState, RunSolvable s ∧ Step s t ∧ ¬ RunSolvable t := by
  exact ⟨heavyGreedySource, heavyGreedyTrap, heavyGreedySource_wins,
    indexedStep_forget (stepAt_sound heavyGreedy_bad_step), heavyGreedyTrap_loses⟩

#print axioms heavyGreedy_nonconfluence
#print axioms heavyGreedyTrap_loses

open Lean Elab Command in
run_cmd do
  let names : List Name := [`LC004.greedyAuditSearch, `LC004.greedyAuditSearch_complete, `LC004.heavyGreedySource, `LC004.heavyGreedyTrap, `LC004.heavyGreedy_bad_step, `LC004.heavyGreedyTrap_loses, `LC004.heavyGreedySource_wins, `LC004.heavyGreedySource_encoding, `LC004.heavyGreedyTrap_encoding, `LC004.heavyGreedy_multiplicities, `LC004.heavyGreedy_nonconfluence]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Forbidden axiom {ax} in {name}"
  logInfo "HEAVY GREEDY AUDIT PASS: 11 declarations"

end LC004

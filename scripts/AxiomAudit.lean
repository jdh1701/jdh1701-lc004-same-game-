import LC004
import Lean.Util.CollectAxioms

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let some owner ← findModuleOf? name | continue
    if owner == `LC004 || `LC004.isPrefixOf owner then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in project declaration {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "Axiom audit found no project declarations"
  logInfo m!"AXIOM AUDIT PASS: {checked} project declarations; only propext, Classical.choice, Quot.sound permitted"

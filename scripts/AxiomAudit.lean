import LC004
import Lean.Util.CollectAxioms

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut compilerStages := 0
  for (name, info) in env.constants.toList do
    let some owner ← findModuleOf? name | continue
    if owner == `LC004 || (`LC004).isPrefixOf owner then
      -- Unsafe compiler transformation stages erase proof fields with
      -- lcProof. They are runtime IR, not logical proof declarations.
      let stageName := (name.toString.splitOn ".").any (fun s => s.startsWith "_cstage")
      if info.isUnsafe && stageName then
        compilerStages := compilerStages + 1
        continue
      if info.isUnsafe || info.isPartial then
        throwError "Unexpected unsafe or partial project declaration {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in project declaration {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "Axiom audit found no project declarations"
  logInfo m!"Compiler-only unsafe transformation stages excluded: {compilerStages}"
  logInfo m!"AXIOM AUDIT PASS: {checked} project declarations; only propext, Classical.choice, Quot.sound permitted"

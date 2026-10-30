import LC004.SeparatorDeletionLink
import Lean.Util.CollectAxioms

/- Reuse the already established PR38 infrastructure. No duplicate
collapse theorem or universal collapsibility assertion is introduced here. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in [``LC004.faceAlternatingSum_elementary_trace,
      ``LC004.winningJoinCoefficient_zero_of_elementary_trace,
      ``LC004.facetFaces_eq_of_mutual_cover,
      ``LC004.facetAlternatingSum_deletion_link,
      ``LC004.winningJoinCoefficient_separator_deletion_link] do
    let some info := env.find? name | throwError "Missing dependency {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected theorem declaration {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Forbidden axiom {ax} in {name}"
  logInfo "EXISTING COLLAPSE DEPENDENCIES AUDIT PASS: five checked declarations"

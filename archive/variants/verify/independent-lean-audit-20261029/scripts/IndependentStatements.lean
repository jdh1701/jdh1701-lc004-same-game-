import LC004
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option format.width 1000000 in
run_cmd do
  let env ← getEnv
  for nm in [``LC004.winningColorPatternCount_second_diagonal,
             ``LC004.winningColorPatternCount_signed_joins,
             ``LC004.raw_max_win_iff_certificate,
             ``LC004.winning_color_pattern_iff_raw_win,
             ``LC004.certificate_heavy_face,
             ``LC004.rigid_face_iff_no_rigid_arc_separator,
             ``LC004.winning_restrict_heavy_face,
             ``LC004.certificate_pattern_determined_by_heavy_faces] do
    let some ci := env.find? nm | throwError "MISSING {nm}"
    let ax ← collectAxioms nm
    logInfo m!"IA_STMT {nm} : {ci.type} || AXIOMS {ax}"

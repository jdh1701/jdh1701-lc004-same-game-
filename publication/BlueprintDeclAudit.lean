import LC004.HeavyFaceCertificateProduct
import Lean.Util.CollectAxioms

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env <- getEnv
  let names : List Name := [
    `LC004.CertificatePartition,
    `LC004.ColorPattern,
    `LC004.FacePathLocality,
    `LC004.HeavyPosition,
    `LC004.PatternNoncrossing,
    `LC004.RigidPosition,
    `LC004.assembledPattern_constraint,
    `LC004.canonical_heavy_face_restrict_join,
    `LC004.certificate_face_saturated,
    `LC004.certificate_heavy_face,
    `LC004.certificate_partition_count_product,
    `LC004.certificate_rigid_block_eq_class,
    `LC004.exists_partition_of_noncrossing_regions,
    `LC004.facePathLocality_of_edge_saturation,
    `LC004.heavyFaceCertificateEquiv,
    `LC004.heavyFaceEmbedding,
    `LC004.heavyFacePositions,
    `LC004.raw_win_heavy_face_word,
    `LC004.raw_win_iff_heavy_face_decomposition,
    `LC004.rigidFacePattern,
    `LC004.rigid_face_iff_no_rigid_arc_separator,
    `LC004.winning_iff_heavy_face_decomposition,
    `LC004.winning_restrict_heavy_face]
  for name in names do
    let some info := env.find? name
      | throwError "Blueprint declaration does not exist: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial Blueprint declaration: {name}"
    let axs <- collectAxioms name
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Forbidden axiom {ax} in Blueprint declaration {name}"
  logInfo m!"BLUEPRINT DECLARATION AUDIT PASS: {names.length} actual declarations"

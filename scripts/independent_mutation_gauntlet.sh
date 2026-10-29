#!/usr/bin/env bash
# Plant known-bad edits and record whether each guard rejects them.
# Reports raw exit codes; nonzero means the guard fired.
set -u
cd "$(git rev-parse --show-toplevel)"
export PATH="$HOME/.elan/bin:$PATH"

note() { echo "::notice title=mutant $1::$2"; }

revert() { git checkout -q -- . ; git clean -fdq LC004 ; }

guards() {
  local label=$1
  lake build LC004 > "mut_$label.build.log" 2>&1; b=$?
  local sw; sw=$(grep -c "declaration uses 'sorry'" "mut_$label.build.log" || true)
  python3 scripts/check_lean_coverage.py > /dev/null 2> "mut_$label.cov.err"; c=$?
  lake env lean scripts/AxiomAudit.lean > "mut_$label.ax.log" 2>&1; a=$?
  lake env lean scripts/FaceAxiomAudit.lean > "mut_$label.face.log" 2>&1; f=$?
  note "$label" "lake_build_exit=$b sorry_warnings=$sw source_guard_exit=$c project_axiom_audit_exit=$a face_axiom_audit_exit=$f"
}

# M1: sorry inside the module closure audited by the face workflow
printf '\ntheorem LC004.planted_m1 : (1 : Nat) = 2 := by sorry\n' >> LC004/RigidFaceGeometry.lean
guards M1_sorry_in_face_closure; revert

# M2: custom axiom plus a theorem that uses it, in the same closure
printf '\naxiom LC004.planted_m2_ax : (1 : Nat) = 2\ntheorem LC004.planted_m2 : (1 : Nat) = 2 := LC004.planted_m2_ax\n' >> LC004/RigidFaceGeometry.lean
guards M2_axiom_in_face_closure; revert

# M3: sorry in a root module OUTSIDE the face-audit closure
printf '\ntheorem LC004.planted_m3 : (1 : Nat) = 2 := by sorry\n' >> LC004/WinningJoinCount.lean
guards M3_sorry_outside_face_closure; revert

# M4: native_decide (semantic axiom Lean.ofReduceBool) in a root module outside the face closure
printf '\ntheorem LC004.planted_m4 : (2 : Nat) + 2 = 4 := by native_decide\n' >> LC004/WinningJoinCount.lean
guards M4_native_decide_outside_face_closure; revert

# M5: orphan module that the root never imports
printf 'import Mathlib\ntheorem planted_orphan : True := trivial\n' > LC004/PlantedOrphan.lean
python3 scripts/check_lean_coverage.py > /dev/null 2> mut_M5.cov.err; c=$?
note M5_orphan_module "source_guard_exit=$c"; revert

# M7: sorry inside the NEW decomposition module (must be caught by every guard)
printf '\ntheorem LC004.planted_m7 : (1 : Nat) = 2 := by sorry\n' >> LC004/HeavyFaceDecomposition.lean
guards M7_sorry_in_new_decomposition_module; revert

# M6: false headline statement (+1 on the right side); proof must fail to compile
sed -i 's/= k \* (2 \* k + 2).choose (k - 1) := by/= k * (2 * k + 2).choose (k - 1) + 1 := by/' LC004/SecondDiagonalClosedForm.lean
if git diff --quiet; then note M6_false_statement "NOOP patch did not apply"; else
  lake build LC004 > mut_M6.build.log 2>&1; b=$?
  note M6_false_statement "lake_build_exit=$b first_error=$(grep -m1 'error' mut_M6.build.log | cut -c1-160)"
fi
revert
exit 0

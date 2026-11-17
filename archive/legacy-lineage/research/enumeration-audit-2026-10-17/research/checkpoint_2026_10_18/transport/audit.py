"""Audit the new theorem inventory and the current literal Lean axiom report.

CI supplies its freshly generated report. Source scans supplement kernel
checking; the explicit open-boundary flags prevent conditional progress
from being reported as a complete enumeration proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MODULES = [f"LC004/{name}.lean" for name in (
    "CoefficientLocality", "CoefficientTransport", "SeparatedPartitions",
    "FullBoardCancellation")]
parser = argparse.ArgumentParser()
parser.add_argument("--axioms-log", type=Path, default=HERE / "logs/axioms_verified.log")
args = parser.parse_args()
names = [name for path in MODULES for name in
         re.findall(r"^theorem (\w+)", (ROOT / path).read_text(), re.M)]
assert len(names) == 23 and len(set(names)) == 23, names
log = args.axioms_log.read_text()
assert "error:" not in log and "sorryAx" not in log
reports = {}
for name, axioms, empty in re.findall(
        r"'LC004\.(\w+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))", log):
    used = [] if empty else [x.strip() for x in axioms.split(",") if x.strip()]
    assert set(used) <= {"propext", "Classical.choice", "Quot.sound"}, (name, used)
    reports[name] = used
assert set(names) == set(reports), (set(names) - set(reports), set(reports) - set(names))
sources = [ROOT / "LC004.lean", *sorted((ROOT / "LC004").glob("*.lean"))]
patterns = {
    "holes": r"\b(?:sorry|admit|sorryAx)\b",
    "custom_axioms": r"^\s*(?:private\s+|protected\s+)?axiom\s",
    "unchecked_code": r"\b(?:unsafe|extern|implemented_by|native_decide)\b",
}
scans = {key: [dict(path=str(path.relative_to(ROOT)), line=i)
               for path in sources for i, line in enumerate(path.read_text().splitlines(), 1)
               if re.search(pattern, line)] for key, pattern in patterns.items()}
assert all(not hits for hits in scans.values()), scans
assert "import LC004.FullBoardCancellation" in (ROOT / "LC004.lean").read_text()
stages = json.loads((HERE.parent / "bridge/STAGES.json").read_text())["stages"]
counts = {status: sum(stage["status"] == status for stage in stages)
          for status in ("verified", "partial", "open")}
assert counts == dict(verified=4, partial=1, open=4)
prior = json.loads((HERE / "data/prior_art_comparison.json").read_text())
assert prior["compared_lengths"] == [12, 13, 14, 15]
assert all(check["all_coefficients_match"] for check in prior["checks"])
assert prior["numerical_formulas_are_new"] is False
result = dict(
    new_theorem_count=len(names), new_named_theorems=names, axiom_reports=reports,
    source_hashes={path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in MODULES},
    scans=scans, stage_counts=counts,
    coefficient_locality_lean_verified=True,
    disjoint_partition_product_order_isomorphism_lean_verified=True,
    full_board_image_family_cancellation_lean_verified=True,
    full_board_all_witness_coverage_lean_verified=False,
    full_board_small_block_theorem_lean_verified=False,
    general_enumeration_solved=False,
    mathematical_originality_established=False,
    numerical_prior_art_correction_recorded=True,
    remaining=[
        "Exhaustive four-position branch classification and endpoint extension/restriction",
        "Discharge hcover for the full valid-witness family",
        "Small-block and component assembly, including size two and three",
        "Executable witness generator and grammar-to-raw-game correspondence",
        "Useful general connected-coefficient law with growth analysis",
        "End-to-end W(q,n) theorem and full originality assessment",
    ],
)
(HERE / "data/source_audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)

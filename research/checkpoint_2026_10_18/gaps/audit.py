"""Audit the new theorem inventory and a literal Lean axiom report.

CI passes the report it has just generated, rather than trusting the saved log.
The source scan supplements kernel checking; it does not replace it.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MODULES = [f"LC004/{name}.lean" for name in (
    "PairGapDecomposition", "WitnessGluing", "FourGapWitnesses",
    "FourGapGeometry", "RegionalCancellation")]
parser = argparse.ArgumentParser()
parser.add_argument("--axioms-log", type=Path, default=HERE / "logs/axioms_verified.log")
args = parser.parse_args()
names = [name for path in MODULES for name in
         re.findall(r"^theorem (\w+)", (ROOT / path).read_text(), re.M)]
assert len(names) == 24 and len(set(names)) == 24, names
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
assert "import LC004.RegionalCancellation" in (ROOT / "LC004.lean").read_text()
stages = json.loads((HERE.parent / "bridge/STAGES.json").read_text())["stages"]
counts = {status: sum(stage["status"] == status for stage in stages)
          for status in ("verified", "partial", "open")}
assert counts == dict(verified=4, partial=1, open=4)
result = dict(
    new_theorem_count=len(names), new_named_theorems=names, axiom_reports=reports,
    source_hashes={path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in MODULES},
    scans=scans, stage_counts=counts,
    regional_four_gap_invariance_lean_verified=True,
    positional_regional_cancellation_lean_verified=True,
    full_board_small_block_theorem_lean_verified=False,
    general_enumeration_solved=False,
    remaining=[
        "Locality/filtering of witnesses at a target full-board partition",
        "Full-board/product order isomorphism and coefficient transport",
        "Exhaustive four-position branch classification and endpoint extension/restriction",
        "Small-block and component assembly, including size two and three",
        "Executable witness generator and raw-game correspondence",
        "Useful general connected-coefficient law with growth analysis",
    ],
)
(HERE / "data/source_audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)

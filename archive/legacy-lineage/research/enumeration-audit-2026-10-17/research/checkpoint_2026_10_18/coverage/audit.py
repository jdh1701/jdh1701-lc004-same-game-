"""Audit the complete-family coefficient theorem and its literal Lean report.

CI passes a freshly generated axiom log. The historical stage snapshot is
left intact; the new snapshot marks the structural stage partial, not complete.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MODULES = [f"LC004/{name}.lean" for name in (
    "WitnessEmbedding", "QuadWitnessClassification", "QuadWitnessGeometry",
    "AllWitnessCancellation")]
parser = argparse.ArgumentParser()
parser.add_argument("--axioms-log", type=Path, default=HERE / "logs/axioms_verified.log")
args = parser.parse_args()
names = [name for path in MODULES for name in re.findall(
    r"^(?:@\[[^\]]+\]\s+)?theorem (\w+)", (ROOT / path).read_text(), re.M)]
assert len(names) == 31 and len(set(names)) == 31, names
log = args.axioms_log.read_text()
assert "error:" not in log and "sorryAx" not in log
reports = {}
for name, axioms, empty in re.findall(
        r"'LC004\.(\w+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))", log):
    used = [] if empty else [x.strip() for x in axioms.split(",") if x.strip()]
    assert set(used) <= {"propext", "Classical.choice", "Quot.sound"}, (name, used)
    reports[name] = used
assert set(names) == set(reports), (set(names) - set(reports), set(reports) - set(names))
sources = [ROOT / "LC004.lean", *sorted((ROOT / "LC004").glob("*.lean")),
           HERE / "PrintAxioms.lean", HERE / "Nonvacuity.lean"]
patterns = {
    "holes": r"\b(?:sorry|admit|sorryAx)\b",
    "custom_axioms": r"^\s*(?:private\s+|protected\s+)?axiom\s",
    "unchecked_code": r"\b(?:unsafe|extern|implemented_by|native_decide)\b",
}
scans = {key: [dict(path=str(path.relative_to(ROOT)), line=i)
               for path in sources for i, line in enumerate(path.read_text().splitlines(), 1)
               if re.search(pattern, line)] for key, pattern in patterns.items()}
assert all(not hits for hits in scans.values()), scans
assert "import LC004.AllWitnessCancellation" in (ROOT / "LC004.lean").read_text()
main_source = (ROOT / "LC004/AllWitnessCancellation.lean").read_text()
signature = main_source.split("theorem all_witness_four_block_zero", 1)[1].split(":= by", 1)[0]
assert "allPairTripleWitnesses n" in signature
assert all(word not in signature for word in ("hcover", "hinv", "regionalFourBlockFamily"))
stages = json.loads((HERE / "STAGES.json").read_text())["stages"]
baseline = json.loads((HERE.parent / "bridge/STAGES.json").read_text())["stages"]
assert [s["id"] for s in stages] == [s["id"] for s in baseline]
assert [s["description"] for s in stages] == [s["description"] for s in baseline]
changed = [s["id"] for s, old in zip(stages, baseline) if s["status"] != old["status"]]
assert changed == ["F"]
counts = {status: sum(stage["status"] == status for stage in stages)
          for status in ("verified", "partial", "open")}
assert counts == dict(verified=4, partial=2, open=3)
result = dict(
    new_theorem_count=len(names), new_named_theorems=names, axiom_reports=reports,
    source_hashes={path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in MODULES},
    scans=scans, stage_counts=counts, changed_stage_statuses=changed,
    stage_definitions_unchanged=True,
    exhaustive_four_position_classification_lean_verified=True,
    full_board_witness_extension_and_restriction_lean_verified=True,
    complete_witness_family_identification_lean_verified=True,
    all_witness_four_block_cancellation_lean_verified=True,
    coverage_assumption_remaining=False,
    minimum_five_connected_support_lean_verified=False,
    executable_generator_identification_lean_verified=False,
    general_enumeration_solved=False,
    mathematical_originality_established=False,
    remaining=[
        "Size-two/three and connected-component assembly for minimum-five support",
        "Complete noncrossing-closure component factorization",
        "Executable witness generator, compression refinement and grammar-to-raw direction",
        "Determine connected coefficients and analyze growth of a useful general method",
        "End-to-end W(q,n) theorem and external originality assessment",
    ],
)
(HERE / "data/source_audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)

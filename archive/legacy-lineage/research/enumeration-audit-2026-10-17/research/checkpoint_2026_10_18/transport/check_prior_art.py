"""Compare existing exact coefficient artifacts with transcribed OEIS formulas.

This is a prior-art comparison, not a new enumeration or a Lean proof.
No network access is needed for CI. The source URL/access date are in the
snapshot; source transcription was checked against the page during the audit.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
source = HERE / "data/oeis_A323844_coefficients.json"
snapshot = json.loads(source.read_text())
references = snapshot["polynomials"]
engine = json.loads((BASE / "factorization/data/engine_checks.json").read_text())
rows = {row["n"]: row for row in engine["rows"]}
checks = []
for n in (12, 13, 14):
    assert rows[n]["polynomial"] == references[str(n)], n
    checks.append(dict(n=n, artifact="factorization/data/engine_checks.json", all_coefficients_match=True))
for n, rel in ((13, "bridge/data/holdout_length13.json"),
               (15, "factorization/data/threshold15.json")):
    data = json.loads((BASE / rel).read_text())
    assert data["n"] == n and data["polynomial"] == references[str(n)], (n, rel)
    checks.append(dict(n=n, artifact=rel, all_coefficients_match=True))
result = dict(
    source_url=snapshot["source_url"], access_date=snapshot["access_date"],
    snapshot_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    compared_lengths=[12, 13, 14, 15], checks=checks,
    numerical_formulas_are_new=False, mathematical_originality_established=False,
    length_16_known_externally=True, new_enumeration_performed=False,
)
(HERE / "data/prior_art_comparison.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)

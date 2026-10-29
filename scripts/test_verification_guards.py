"""Exercise the coverage and axiom guards with deliberate negative cases.

No unproved mathematical declaration is introduced: the audit negative case
only removes Quot.sound from a temporary copy of the allowed-name list.
"""
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
sentinel = root / 'LC004' / '_CoverageGuardRegression.lean'
with sentinel.open('x') as stream:
    stream.write('import Mathlib\n')
try:
    result = subprocess.run(['python3', 'scripts/check_lean_coverage.py'],
                            cwd=root, capture_output=True, text=True)
    assert result.returncode != 0 and '_CoverageGuardRegression' in result.stderr, result
finally:
    sentinel.unlink()
print('NEGATIVE COVERAGE CHECK PASS: unimported active module rejected', flush=True)

source = (root / 'scripts/AxiomAudit.lean').read_text()
assert source.count('ax == `Quot.sound') == 1
source = source.replace('ax == `Quot.sound', 'ax == `deliberatelyExcludedStandardAxiom')
with tempfile.TemporaryDirectory(prefix='lc004-audit-negative-') as temp:
    path = Path(temp) / 'AuditNegative.lean'
    path.write_text(source)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                            capture_output=True, text=True)
    combined = result.stdout + result.stderr
    assert result.returncode != 0 and 'Forbidden axiom Quot.sound' in combined, combined
print('NEGATIVE AXIOM CHECK PASS: disallowed dependency rejected', flush=True)

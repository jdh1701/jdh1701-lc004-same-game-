"""Static/source and saved-result audit; Lean verification is separate."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
modules=['LC004/CoefficientFactorization.lean','LC004/NoncrossingRestriction.lean']
names=[n for p in modules for n in re.findall(r'^theorem (\w+)',(ROOT/p).read_text(),re.M)]
assert len(names)==11
logs=(HERE/'logs/axioms_verified.log').read_text()
assert 'sorryAx' not in logs and 'error:' not in logs
for n in names:
    assert f"'LC004.{n}' depends on axioms:" in logs,n
files=[ROOT/'LC004.lean',*sorted((ROOT/'LC004').glob('*.lean'))]
patterns={'holes':r'\b(?:sorry|admit|sorryAx)\b',
          'custom_axioms':r'^\s*(?:private\s+|protected\s+)?axiom\s',
          'unsafe':r'\b(?:unsafe|extern|implemented_by|native_decide)\b'}
scans={k:[dict(path=str(p.relative_to(ROOT)),line=i) for p in files
          for i,line in enumerate(p.read_text().splitlines(),1) if re.search(pattern,line)]
       for k,pattern in patterns.items()}
assert all(not v for v in scans.values()),scans
stage_data=json.loads((HERE.parent/'bridge/STAGES.json').read_text())
counts={s:sum(x['status']==s for x in stage_data['stages']) for s in ('verified','partial','open')}
assert counts==dict(verified=4,partial=1,open=4)
out=dict(new_named_theorems=names,new_theorem_count=len(names),stage_counts=counts,
    source_hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in modules},
    scans=scans,remaining='Assemble partition-ideal product equivalence, coefficient transport, and generator correspondence; prove small-block cancellation and derive a useful complete recurrence.')
(HERE/'data/source_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)

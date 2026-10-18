"""Source and evidence inventory; compiler output is separate verification."""
from pathlib import Path
import json,re,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
modules=['LC004/CoefficientBarrier.lean','LC004/UnionCoefficientIdentity.lean',
         'LC004/FourBlockCancellation.lean','LC004/ChordBarrier.lean']
names=[n for p in modules for n in re.findall(r'^theorem (\w+)',(ROOT/p).read_text(),re.M)]
assert len(names)==12,names
log=(HERE/'logs/axioms_verified.log').read_text()
assert 'error:' not in log and 'sorryAx' not in log
for n in names: assert f"'LC004.{n}'" in log,n
files=[ROOT/'LC004.lean',*sorted((ROOT/'LC004').glob('*.lean'))]
patterns={'holes':r'\b(?:sorry|admit|sorryAx)\b',
          'custom_axioms':r'^\s*(?:private\s+|protected\s+)?axiom\s',
          'unsafe':r'\b(?:unsafe|extern|implemented_by|native_decide)\b'}
scans={k:[dict(path=str(p.relative_to(ROOT)),line=i) for p in files
          for i,line in enumerate(p.read_text().splitlines(),1) if re.search(pattern,line)]
       for k,pattern in patterns.items()}
assert all(not v for v in scans.values()),scans
stages=json.loads((HERE.parent/'bridge/STAGES.json').read_text())['stages']
counts={s:sum(x['status']==s for x in stages) for s in ('verified','partial','open')}
assert counts==dict(verified=4,partial=1,open=4)
tests=json.loads((HERE/'data/small_block_checks.json').read_text())
assert tests['unexpected_failures']==0
assert sum(tests['checks'][f'block_{m}_coefficient_checks'] for m in (2,3,4))==105366
assert tests['checks']['rotation_support_checks']==9285
assert tests['size_five_counterexample']['actual']==-1
assert tests['size_five_counterexample']['small_block_prediction']==0
result=dict(new_theorem_count=len(names),new_named_theorems=names,stage_counts=counts,
    source_hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in modules},
    scans=scans,minimum_five_theorem_lean_verified=False,
    remaining='Discharge four-gap invariance for the full witness family, locality, product/rotation transport, and generator correspondence.')
(HERE/'data/source_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)

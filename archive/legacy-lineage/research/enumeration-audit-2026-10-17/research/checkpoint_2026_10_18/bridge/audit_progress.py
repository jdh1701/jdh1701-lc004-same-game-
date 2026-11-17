#!/usr/bin/env python3
"""Report the fixed stage count and exact source declarations added this pass.

The source scan is not a replacement for the Lean build and axiom report.
It also checks that extracting RawGame did not alter the existing model bodies.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = 'c04443b029ff85da4fad7ecc65f2d6e29f9aabb2'
stage_data = json.loads((HERE/'STAGES.json').read_text())
counts = Counter(s['status'] for s in stage_data['stages'])
assert counts == {'verified':4,'partial':1,'open':4}
sources = ['LC004/GrammarInsertion.lean','LC004/OrdinaryGrammarComplete.lean']
names = [name for p in sources for name in
         re.findall(r'^theorem (\w+)',(ROOT/p).read_text(),re.M)]
assert len(names) == 12
baseline = json.loads((HERE/'data/raw_model_baseline.json').read_text())
assert baseline['base_commit'] == BASE
current = (ROOT/'LC004/RawGame.lean').read_text()
definition_controls = {}
for name in ['ordinaryStepAtFuel','ordinaryStepAt','ordinaryFollow','OrdinarySolvable']:
    pattern = rf'^def {name}\b.*?(?=\n\n)'
    new_body = re.search(pattern,current,re.M|re.S).group()
    digest = hashlib.sha256(new_body.encode()).hexdigest()
    assert baseline['definition_sha256'][name] == digest, name
    definition_controls[name] = digest
files = [ROOT/'LC004.lean',*sorted((ROOT/'LC004').glob('*.lean'))]
patterns = {'holes':r'\b(?:sorry|admit|sorryAx)\b',
            'project_axioms':r'^\s*(?:private\s+|protected\s+)?axiom\s',
            'unsafe_overrides':r'\b(?:unsafe|extern|implemented_by)\b',
            'native_computation':r'\bnative_decide\b'}
scans = {kind:[{'path':str(p.relative_to(ROOT)),'line':i}
               for p in files for i,line in enumerate(p.read_text().splitlines(),1)
               if re.search(pattern,line)] for kind,pattern in patterns.items()}
assert all(not x for x in scans.values()),scans
result = dict(total_stages=len(stage_data['stages']),stage_counts=dict(counts),
              new_named_theorems=names,new_theorem_count=len(names),
              unchanged_raw_definition_hashes=definition_controls,
              source_hashes={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                             for p in sources},source_scans=scans,
              evidence='Lean compiler output and full GitHub build are separate verification evidence.')
(HERE/'data/progress_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)

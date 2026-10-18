#!/usr/bin/env python3
"""Record sources and import coverage; compiler axiom reports are separate."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
files = [ROOT/'LC004.lean', *sorted((ROOT/'LC004').glob('*.lean'))]
patterns = {'holes': r'\b(?:sorry|admit|sorryAx)\b',
            'project_axioms': r'^\s*(?:private\s+|protected\s+)?axiom\s',
            'unsafe_overrides': r'\b(?:unsafe|extern|implemented_by)\b',
            'native_computation': r'\bnative_decide\b'}
scans = {name: [{'path': str(p.relative_to(ROOT)), 'line': n}
                for p in files for n,line in enumerate(p.read_text().splitlines(),1)
                if re.search(pattern,line)] for name,pattern in patterns.items()}
assert all(not values for values in scans.values()), scans
reachable = set()
def visit(module):
    if module in reachable:
        return
    reachable.add(module)
    source = ROOT/(module.replace('.','/')+'.lean')
    for imported in re.findall(r'^import (LC004(?:\.[\w]+)*)\s*$',source.read_text(),re.M):
        visit(imported)
visit('LC004')
result = {'base_commit': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
          'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
          'reachable_modules': sorted(reachable), 'scans': scans,
          'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
          'manifest_sha256': hashlib.sha256((ROOT/'lake-manifest.json').read_bytes()).hexdigest(),
          'scope': 'Static audit; root builds and axiom printouts supply formal verification evidence.'}
(HERE/'data/source_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'source_files':len(files),'reachable_modules':len(reachable),'scans':scans}))

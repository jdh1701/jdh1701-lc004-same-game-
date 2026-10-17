#!/usr/bin/env python3
"""Source provenance and project import-closure audit; not a Lean checker."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()


def run():
    files=[ROOT/'LC004.lean',*sorted((ROOT/'LC004').glob('*.lean'))]
    reachable=set()
    def visit(module):
        if module in reachable:return
        reachable.add(module)
        path=ROOT/(module.replace('.','/')+'.lean')
        assert path.is_file(),('missing import',module)
        for child in re.findall(r'^import (LC004(?:\.[A-Za-z0-9_]+)*)\s*$',path.read_text(),re.M):
            visit(child)
    visit('LC004')
    scans={}
    for label,pattern in {
        'sorry_admit_sorryAx':r'\b(?:sorry|admit|sorryAx)\b',
        'project_axiom_declaration':r'^\s*(?:private\s+|protected\s+)?axiom\s',
        'unsafe_extern_implemented_by':r'\b(?:unsafe|extern|implemented_by)\b',
        'native_decide':r'\bnative_decide\b',
    }.items():
        hits=[]
        for p in files:
            for line_no,line in enumerate(p.read_text().splitlines(),1):
                if re.search(pattern,line):
                    hits.append({'file':str(p.relative_to(ROOT)),'line':line_no,'text':line})
        scans[label]=hits
    result={
        'recorded_head_before_checkpoint_commit':git('rev-parse','HEAD'),
        'baseline_commit':'a9cb335c11b795372b7a4d22b68c6c4fab83239c',
        'other_branch_heads':{b:git('rev-parse',b) for b in (
            'origin/research/post-theorem-wub-census-2026-09-23',
            'origin/research/consolidated-333-lean')},
        'toolchain':(ROOT/'lean-toolchain').read_text().strip(),
        'manifest_sha256':hashlib.sha256((ROOT/'lake-manifest.json').read_bytes()).hexdigest(),
        'reachable_project_modules':sorted(reachable),
        'scans':scans,
        'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in files},
        'limitations':['Text scans do not establish theorem correctness.',
          'Lean axiom output and source semantics must be checked separately.',
          'Raw-word commuting theorem is not supplied by this checkpoint.'],
    }
    assert all(not hits for hits in scans.values()),scans
    assert 'LC004.UniqueMedian' in reachable
    (HERE/'data/source_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'reachable_modules':len(reachable),'scans':scans,
                      'manifest_sha256':result['manifest_sha256']}))


if __name__=='__main__':run()

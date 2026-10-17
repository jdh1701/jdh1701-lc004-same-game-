#!/usr/bin/env python3
"""Execute the checkpoint, preserving literal combined stdout/stderr and status.

Requires the pinned Lean toolchain and `lake exe cache get` first. In the
restricted host used for discovery only, see README for the process-path shim.
"""
from pathlib import Path
import json
import subprocess
import time

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
COMMANDS=[
    ['python3','--version'],['git','--version'],['lake','env','lean','--version'],
    ['lake','build'],
    ['lake','env','lean',str(HERE.relative_to(ROOT)/'PrintAxioms.lean')],
    ['python3','scripts/exhaustive_verify.py'],
    ['python3','research/exhaustive_structure.py'],
    *[['python3',str(HERE.relative_to(ROOT)/f)] for f in (
       'experiments.py','orbit_experiments.py','hypothesis_tests.py',
       'binary_unique_conjecture.py','reference_checks.py','source_audit.py')],
]


def run():
    rows=[]
    for number,command in enumerate(COMMANDS):
        filename=HERE/'logs'/f'reproduction_{number:02d}.log'
        start=time.monotonic()
        with filename.open('w') as log:
            log.write('COMMAND_JSON='+json.dumps(command)+'\n');log.flush()
            result=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
            elapsed=time.monotonic()-start
            log.write(f'\nEXIT_CODE={result.returncode}\nELAPSED_SECONDS={elapsed}\n')
        rows.append(dict(command=command,returncode=result.returncode,
                         elapsed_seconds=elapsed,log=str(filename.relative_to(ROOT))))
        print(json.dumps(rows[-1]),flush=True)
        if result.returncode:break
    (HERE/'data/reproduction_status.json').write_text(json.dumps(rows,indent=2)+'\n')
    if rows[-1]['returncode']:raise SystemExit(rows[-1]['returncode'])


if __name__=='__main__':run()

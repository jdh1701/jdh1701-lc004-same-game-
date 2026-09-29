"""Build every inventoried Lean module and audit every named theorem; fail closed."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
report = {'status': 'not_run', 'python_test_inventory_count': 333,
          'python_implementation_verified': False, 'all_mathematical_obligations_closed': False,
          'commands': [], 'theorems': [], 'audit_controls': []}

def execute(args, directory):
    try:
        p = subprocess.run(args, cwd=directory, text=True, capture_output=True, timeout=180)
        row = dict(command=args, returncode=p.returncode, stdout=p.stdout, stderr=p.stderr)
    except (OSError, subprocess.TimeoutExpired) as e:
        row = dict(command=args, returncode=-1, stdout='', stderr=str(e))
    report['commands'].append(row)
    print(json.dumps(row), flush=True)
    return row

def hashes_ok():
    return all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest() == h
               for p,h in json.loads((ROOT/'source-hashes.json').read_text()).items())

def main():
    if not hashes_ok():
        report['status'] = 'source_hash_mismatch'; return 1
    lake = shutil.which('lake')
    if not lake:
        report['status'] = 'blocked_lake_missing'; return 1
    project = ROOT/'pvsnp_foundation'
    version = execute([lake,'env','lean','--version'], project)
    if version['returncode'] or 'version 4.34.0' not in version['stdout']:
        report['status'] = 'toolchain_failed'; return 1
    execute([lake,'--version'], project)
    auditor = execute([lake,'build'], ROOT/'auditor')
    targets = json.loads((ROOT/'targets.json').read_text())
    controls_module = 'AlexandriaComplexity.AuditNegativeControls'
    control_build = execute([lake, 'build', controls_module], project)
    if auditor['returncode'] == 0 and control_build['returncode'] == 0:
        for name, expected_code, expected_axioms in [
            ('acceptedProof', 0, []),
            ('rejectedProof', 1, ['AlexandriaAuditControls.untrustedTestAxiom']),
            ('rejectedExtensionality', 1, ['propext']),
            ('rejectedDefinition', 2, None),
            ('missingDeclaration', 2, None),
        ]:
            declaration = 'AlexandriaAuditControls.' + name
            result = execute([lake, 'env', '../auditor/.lake/build/bin/alexandria-lean-audit',
                              '--module', controls_module, '--declaration', declaration], project)
            try:
                receipt = json.loads(result['stdout'])
                passed = result['returncode'] == expected_code
                if expected_axioms is not None:
                    passed = (passed and receipt.get('axioms') == expected_axioms
                              and receipt.get('unresolved_assumptions') == expected_axioms
                              and receipt.get('declaration') == declaration
                              and receipt.get('declaration_kind') == 'theorem'
                              and receipt.get('kernel_checked') is True
                              and receipt.get('ok') is (expected_code == 0))
                else:
                    passed = passed and receipt.get('ok') is False and bool(receipt.get('error'))
            except (ValueError, AttributeError):
                passed = False
            report['audit_controls'].append({'declaration': declaration, 'passed': passed})
    builds = {}
    for module in sorted({t['module'] for t in targets}):
        builds[module] = execute([lake,'build',module], project)['returncode'] == 0
    for t in targets:
        row = dict(t, status='blocked_build')
        if builds[t['module']] and auditor['returncode'] == 0:
            result = execute([lake,'env','../auditor/.lake/build/bin/alexandria-lean-audit',
                              '--module',t['module'],'--declaration',t['declaration']],project)
            try:
                receipt = json.loads(result['stdout'])
                ok = (result['returncode'] == 0 and receipt.get('ok') is True
                      and receipt.get('kernel_checked') is True
                      and receipt.get('declaration_kind') == 'theorem'
                      and receipt.get('declaration') == t['declaration']
                      and receipt.get('axioms') == []
                      and receipt.get('unresolved_assumptions') == [])
                row.update(status='passed' if ok else 'failed_audit', receipt=receipt)
            except (ValueError, AttributeError):
                row['status'] = 'invalid_audit'
        report['theorems'].append(row)
    ok = (hashes_ok() and all(t['status']=='passed' for t in report['theorems'])
          and len(report['audit_controls']) == 5
          and all(t['passed'] for t in report['audit_controls']))
    report['status'] = 'all_existing_theorems_passed' if ok else 'failed_or_blocked'
    return 0 if ok else 1

if __name__=='__main__':
    code = 1
    try:
        code = main()
    finally:
        (ROOT/'lean-report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({'status':report['status'],'passed':sum(t['status']=='passed' for t in report['theorems']), 'total':len(report['theorems'])}))
    sys.exit(code)

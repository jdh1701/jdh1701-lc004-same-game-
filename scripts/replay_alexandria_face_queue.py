"""Replay the continuation queue with an existing, frozen Alexandria Core checkout."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
import time

EXPECTED = {
    'alexandria_core/models.py': 'f919a00c5757b59495ebae808e52836cbbcbf29afc77dbeac2e125dae7ba66db',
    'alexandria_core/campaign.py': 'fcfac224857c04bbcaeacaca16e1a7ad381b8c94f9684ecb788b042a7f8ce6c8',
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--core-root', type=Path, required=True)
    args = parser.parse_args()
    core = args.core_root.resolve()
    hashes = {p: hashlib.sha256((core / p).read_bytes()).hexdigest() for p in EXPECTED}
    if hashes != EXPECTED:
        raise SystemExit('Core source differs from frozen integration checkpoint')
    sys.path.insert(0, str(core))
    from alexandria_core.campaign import plan_campaign, verify_campaign_plan
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / 'research/alexandria_face_queue.json').read_text())
    start = time.perf_counter()
    plan = plan_campaign(manifest)
    assert verify_campaign_plan(plan)[0]
    for _ in range(25):
        assert plan_campaign(manifest) == plan
    altered = copy.deepcopy(plan)
    altered['verified_task_count'] = 1
    assert not verify_campaign_plan(altered)[0]
    receipt = {
        'core_repository': 'jdh1701/Alexandria_Omega_New',
        'core_commit': 'fb413043cb0f4369615132e014691782a344af8a',
        'source_subset': hashes,
        'unchanged_core_source': True,
        'planning_repetitions': 26,
        'deterministic': True,
        'forged_verification_counter_rejected': True,
        'elapsed_seconds': time.perf_counter() - start,
        'discovery_speedup_measured': False,
        'core_code_modified': False,
        'formal_authority_receipt_issued': False,
    }
    for name, data in [('alexandria_face_plan.json', plan),
                       ('alexandria_queue_receipt.json', receipt)]:
        (root / 'research' / name).write_text(json.dumps(data, indent=2) + '\n')
    print('CORE QUEUE PASS: deterministic plan; fabricated verification count rejected')


if __name__ == '__main__':
    main()

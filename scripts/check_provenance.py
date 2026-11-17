#!/usr/bin/env python3
"""Check that every file carried over from the old repository is byte-identical
to the Git blob recorded in docs/provenance.json. Standard library only.
Usage: python3 scripts/check_provenance.py [--list-changed]"""
import hashlib, json, os, sys
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
data = json.load(open(os.path.join(root, 'docs', 'provenance.json')))
bad, missing = [], []
for path, rec in data['files'].items():
    fp = os.path.join(root, path)
    if not os.path.isfile(fp):
        missing.append(path); continue
    raw = open(fp, 'rb').read()
    if hashlib.sha1(b'blob %d\0' % len(raw) + raw).hexdigest() != rec['blob']:
        bad.append(path)
print(f"{len(data['files'])} recorded files: {len(bad)} changed, {len(missing)} missing")
for p in bad: print('CHANGED', p)
for p in missing: print('MISSING', p)
sys.exit(1 if (bad or missing) else 0)

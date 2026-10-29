"""Fail if any active LC004 module lies outside the root import closure."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
seen, pending = set(), ['LC004']
while pending:
    mod = pending.pop()
    if mod in seen:
        continue
    source = root / (mod.replace('.', '/') + '.lean')
    if not source.is_file():
        raise SystemExit(f'Missing local module: {mod}')
    seen.add(mod)
    for line in source.read_text().splitlines():
        match = re.match(r'^\s*import\s+([^/-]+)', line)
        if match:
            pending.extend(name for name in match[1].split()
                           if name == 'LC004' or name.startswith('LC004.'))
all_modules = {'LC004.' + '.'.join(p.relative_to(root / 'LC004').with_suffix('').parts)
               for p in (root / 'LC004').rglob('*.lean')}
missing = sorted(all_modules - seen)
if missing:
    raise SystemExit('Active modules outside the build closure: ' + ', '.join(missing))
print(f'COVERAGE PASS: {len(all_modules)} active modules all reachable from LC004.lean')
print(json.dumps({'root': 'LC004', 'active_modules': sorted(all_modules)}, indent=2))

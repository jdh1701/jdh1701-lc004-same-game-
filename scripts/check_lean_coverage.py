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

# Remove comments and strings before checking forbidden proof keywords.
# Lean block comments nest; a single non-greedy regex would be incorrect.
def logical_source(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

for source in (root / 'LC004').rglob('*.lean'):
    bad = re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|partial)\b',
                    logical_source(source.read_text()))
    if bad:
        raise SystemExit(f'Forbidden source keyword {bad[0]} in {source.relative_to(root)}')
print('SOURCE GUARD PASS: no placeholders, custom axioms, unsafe or partial source')

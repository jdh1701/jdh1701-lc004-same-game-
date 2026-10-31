"""Exhaustive TWO-generator first-excess enumeration and original replay.

This does not assume that every nonzero first-excess pattern has two or three
generators. The reported combined n26 total is a lower bound, not a census.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import tempfile

from prepare import HERE, ROOT, prepare, normalize
from core import generators, join_value


def rotations(p):
    return {normalize(p[i:]+p[:i]) for i in range(len(p))}


def previous_set(j):
    if j == 2:
        return set()
    if j == 3:
        d = json.loads((ROOT/'research/first_excess_20261030/classification.json').read_text())
        ps = [tuple(r['p']) for r in d['dihedral_representatives'] if len(r['generators']) == 2]
    elif j == 4:
        d = json.loads((ROOT/'research/first_excess_20261031/replay.json').read_text())
        ps = [tuple(r['p']) for r in d['rows'] if r['generators'] == 2]
    else:
        raise ValueError(j)
    return set().union(*(rotations(q) for p in ps for q in (p,p[::-1])))


def main():
    prepare()
    results = {'scope': 'complete two-generator full-join connected first-excess family',
               'not_full_first_excess_census': True, 'sizes': []}
    known = {2: 0, 3: 88, 4: 2121}
    with tempfile.TemporaryDirectory(prefix='lc004-two-generator-') as t:
        temp = Path(t)
        search, replay = temp/'search', temp/'replay'
        for source, exe in [('search.cpp',search),('replay.cpp',replay)]:
            subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra','-Werror',str(HERE/source),'-o',str(exe)],check=True)
        for j in range(2,6):
            witness = temp/'witness.txt'
            count = json.loads(subprocess.check_output([str(search),str(j),str(HERE),str(witness)]))
            verified = json.loads(subprocess.check_output([str(replay),str(j),str(witness)]))
            assert verified['original_complete_family_replays'] == sum(r['accepted'] for r in count['layers'])
            if j <= 4:
                baseline = temp/'unpruned.txt'
                other = json.loads(subprocess.check_output([str(search),str(j),str(HERE),str(baseline),'no-scc']))
                assert other == count and baseline.read_bytes() == witness.read_bytes()
                assert count['two_generator_first_excess'] == known[j]
            digest, expanded, samples, seen_types = sha256(), set(), [], set()
            per_k = Counter()
            with witness.open('rb') as f:
                for line in f:
                    digest.update(line)
                    k, typ, *p = map(int,line.split())
                    per_k[k] += 1
                    expanded.update(rotations(tuple(p)))
                    if typ not in seen_types:
                        samples.append(line.decode())
                        fs,_,_ = generators(normalize(p))
                        assert len(fs) == 2 and join_value(fs,normalize(p)) == -1
                        seen_types.add(typ)
            for layer in count['layers']:
                k = layer['six_core_vertices']
                assert per_k[k] == layer['accepted']
                assert layer['original_patterns']*(3*(j-1)+k) == (5*j+1)*layer['accepted']
            assert len(expanded) == count['two_generator_first_excess']
            if j <= 4:
                assert expanded == previous_set(j)
            if j == 5:
                initial = json.loads((HERE/'initial-unfiltered-probe.json').read_text())
                assert digest.hexdigest() == initial['witness_sha256']
                assert len(expanded) == initial['two_generator_total']
            (HERE/f'sample_{j}.txt').write_text(''.join(samples))
            record = {**count, **verified, 'explicit_rotation_union': len(expanded),
                      'python_original_samples':len(samples),'witness_sha256':digest.hexdigest()}
            results['sizes'].append(record)
            print(json.dumps(record,sort_keys=True),flush=True)
    results['n26_disjoint_proved_families'] = {
        'two_generators':results['sizes'][-1]['two_generator_first_excess'],
        'unique_three_run':67132,
        'combined_lower_bound':results['sizes'][-1]['two_generator_first_excess']+67132,
        'exhausts_all_nonzero_first_excess_patterns':'NOT PROVED'}
    (HERE/'checks.json').write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    print('PASS complete two-generator enumeration; original replay; prior-census set equality')


if __name__ == '__main__':
    main()

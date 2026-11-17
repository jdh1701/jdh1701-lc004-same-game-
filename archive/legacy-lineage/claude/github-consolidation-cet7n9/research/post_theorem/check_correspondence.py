"""Independent raw-word versus LC004 Boolean-run transition check.

Source checkpoint: public jdh1701-lc004-same-game- at 9204f839a68a8a7321fbcee1b9745784a1684788.
The oracle deletes a maximal run by raw cell slices and never calls the
Boolean transition implementation. Run-state step mirrors ExecutableStep.lean.
"""

from collections import Counter
from functools import lru_cache
from itertools import product
import json


def runs(word):
    out = []
    for c in word:
        if out and out[-1][0] == c:
            out[-1] = (c, out[-1][1] + 1)
        else:
            out.append((c, 1))
    return tuple(out)


def encode(word):
    return tuple((c, length >= 2) for c, length in runs(word))


def raw_moves(word):
    offset = 0
    for i, (c, length) in enumerate(runs(word)):
        if length >= 2:
            yield i, word[:offset] + word[offset + length:]
        offset += length


def state_step(state, index):
    """Exact normalization-sensitive behavior of LC004.stepAt."""
    if index >= len(state) or not state[index][1]:
        return None
    left, right = state[:index], state[index + 1:]
    if left and right and left[-1][0] == right[0][0]:
        return left[:-1] + ((left[-1][0], True),) + right[1:]
    return left + right


@lru_cache(None)
def raw_path_count(word):
    if not word:
        return 1
    return sum(raw_path_count(child) for _, child in raw_moves(word))


@lru_cache(None)
def state_path_count(state):
    if not state:
        return 1
    return sum(state_path_count(child) for i in range(len(state))
               if (child := state_step(state, i)) is not None)


def audit(q, max_n):
    counts = Counter()
    for n in range(max_n + 1):
        for word in product(range(q), repeat=n):
            state = encode(word)
            rr = dict(raw_moves(word))
            ss = {i: state_step(state, i) for i in range(len(state))
                  if state_step(state, i) is not None}
            counts['words'] += 1
            counts[f'length_{n}'] += 1
            if any(state[i][0] == state[i+1][0] for i in range(len(state)-1)):
                return {'error':'non-normalized', 'q':q,'word':word, 'state':state}
            if rr.keys() != ss.keys():
                return {'error':'legal indices', 'q':q,'word':word,
                        'raw':list(rr), 'state':list(ss)}
            for i, child in rr.items():
                if encode(child) != ss[i]:
                    return {'error':'successor', 'q':q,'word':word,'index':i,
                            'raw_successor':child, 'raw_encoded':encode(child),
                            'state_successor':ss[i]}
                counts['edges'] += 1
            if (raw_path_count(word) != state_path_count(state)):
                return {'error':'path count', 'q':q,'word':word,
                        'raw_paths':raw_path_count(word),
                        'state_paths':state_path_count(state)}
            counts['paths_checked'] += 1
    return {'q': q, 'max_n': max_n, 'counts': dict(sorted(counts.items()))}


if __name__ == '__main__':
    for q, n in ((2, 16), (3, 12), (4, 10)):
        print(json.dumps(audit(q, n), sort_keys=True), flush=True)

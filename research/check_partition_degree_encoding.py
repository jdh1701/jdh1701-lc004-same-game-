"""Exhaustively check the proposed refined NC counting bridge for n <= 10.

Independent finite objects are generated on both sides: fixed-profile set
partitions and degree words. This is evidence for the next Lean bijection,
not a proof of that bijection or the universal refined count.
"""
from collections import Counter
from itertools import combinations
from math import comb


def partitions_with_sizes(positions, sizes):
    if not positions:
        if not sizes:
            yield ()
        return
    first, *rest = positions
    for size in sorted(set(sizes)):
        if size > len(positions):
            continue
        remaining_sizes = list(sizes)
        remaining_sizes.remove(size)
        for tail in combinations(rest, size - 1):
            block = (first, *tail)
            selected = set(block)
            remaining = tuple(i for i in positions if i not in selected)
            for others in partitions_with_sizes(remaining, tuple(remaining_sizes)):
                yield (block, *others)


def noncrossing(blocks):
    for i, left in enumerate(blocks):
        for right in blocks[i + 1:]:
            for a, c in combinations(left, 2):
                for b, d in combinations(right, 2):
                    if a < b < c < d or b < a < d < c:
                        return False
    return True


def degrees(blocks, n):
    result = [0] * (n + 1)
    for block in blocks:
        result[min(block)] = len(block)
    return tuple(result)


def multiset_words(counts, prefix=()):
    if not any(counts.values()):
        yield prefix
        return
    for value in sorted(counts):
        if counts[value]:
            counts[value] -= 1
            yield from multiset_words(counts, (*prefix, value))
            counts[value] += 1


def rooted(word):
    mass = 0
    for cut, degree in enumerate(word, 1):
        mass += degree
        if cut < len(word) and mass < cut:
            return False
    return mass == len(word) - 1


def check(k, profile):
    n = 2 * k + 2
    sizes = (4, *((2,) * (k - 1))) if profile == 'four' else (
        3, 3, *((2,) * (k - 2)))
    encoded = {}
    for partition in partitions_with_sizes(tuple(range(n)), sizes):
        if noncrossing(partition):
            word = degrees(partition, n)
            assert rooted(word)
            assert word not in encoded, (partition, encoded.get(word))
            encoded[word] = partition

    counts = Counter(sizes)
    counts[0] = n + 1 - len(sizes)
    words = set(multiset_words(counts))
    tree_words = {word for word in words if rooted(word)}
    assert set(encoded) == tree_words
    # Check the entire rotation action, including uniqueness of the root.
    for word in words:
        rotations = {word[i:] + word[:i] for i in range(n + 1)}
        assert len(rotations) == n + 1
        assert sum(rooted(rotation) for rotation in rotations) == 1
    assert len(words) == (n + 1) * len(encoded)
    expected = comb(n, k - 1)
    if profile == 'two_triples':
        expected = (k - 1) * expected // 2
    assert len(encoded) == expected
    print('PASS', profile, 'k', k, 'partitions', len(encoded),
          'degree_words', len(words), 'orbit_size', n + 1, flush=True)


if __name__ == '__main__':
    for k in range(2, 5):
        for profile in ('four', 'two_triples'):
            check(k, profile)

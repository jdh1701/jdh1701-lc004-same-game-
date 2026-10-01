"""Exact small-word audit of Biedl et al. §2.2 (arXiv:cs/0107031v1).

The printed CFG is S -> eps | SS | cSc | cScSc for each color c.
It has infinitely many parse trees for any accepted word via nullable SS.
`proper_parses` adopts the explicit convention that both children of SS
derive nonempty strings; all other productions retain their nullable S.
This convention changes the grammar's parse-tree count, not its language.
"""

from functools import cache
from itertools import product


@cache
def path_count(word: str) -> int:
    if not word:
        return 1
    total = 0
    i = 0
    while i < len(word):
        j = i + 1
        while j < len(word) and word[j] == word[i]:
            j += 1
        if j - i >= 2:
            total += path_count(word[:i] + word[j:])
        i = j
    return total


@cache
def proper_parses(word: str) -> int:
    n = len(word)
    if not n:
        return 1
    total = sum(proper_parses(word[:j]) * proper_parses(word[j:])
                for j in range(1, n))
    if n >= 2 and word[0] == word[-1]:
        total += proper_parses(word[1:-1])
    if n >= 3 and word[0] == word[-1]:
        for j in range(1, n - 1):
            if word[j] == word[0]:
                total += proper_parses(word[1:j]) * proper_parses(word[j + 1:-1])
    return total


def census(q: int, max_n: int) -> None:
    labels = 'abcdefghijklmnopqrstuvwxyz'[:q]
    for n in range(max_n + 1):
        counts = {(1, 1): 0, (1, 2): 0, (2, 1): 0, (2, 2): 0}
        examples = {}
        mismatch_language = []
        for letters in product(labels, repeat=n):
            word = ''.join(letters)
            p, g = path_count(word), proper_parses(word)
            if (p > 0) != (g > 0):
                mismatch_language.append((word, p, g))
            if p:
                key = (1 if p == 1 else 2, 1 if g == 1 else 2)
                counts[key] += 1
                examples.setdefault(key, (word, p, g))
        print(q, n, counts, examples, 'language_mismatch', mismatch_language[:3])


if __name__ == '__main__':
    census(2, 10)
    census(3, 8)

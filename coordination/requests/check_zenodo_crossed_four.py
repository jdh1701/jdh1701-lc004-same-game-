"""Small independent audit of the four-gap identity using legal moves and Möbius inversion."""
from collections import Counter
from functools import cache
from itertools import combinations, groupby, product
from math import factorial, prod


@cache
def partitions(n):
    if n == 0:
        return ((),)
    return tuple(word + (color,) for word in partitions(n - 1)
                 for color in range(max(word, default=-1) + 2))


def canonical(word):
    names = {}
    return tuple(names.setdefault(key, len(names)) for key in word)


@cache
def wins(word):
    if not word:
        return True
    start = 0
    for _, group in groupby(word):
        stop = start + sum(1 for _ in group)
        if stop - start >= 2 and wins(canonical(word[:start] + word[stop:])):
            return True
        start = stop
    return False


def refinements(blocks):
    for choices in product(*(partitions(len(b)) for b in blocks)):
        labels = [None] * sum(map(len, blocks))
        for i, (block, part) in enumerate(zip(blocks, choices)):
            for pos, color in zip(block, part):
                labels[pos] = (i, color)
        # Product of partition-lattice Möbius factors from this refinement to the target.
        counts = [1 + max(part) for part in choices]
        yield canonical(labels), prod((-1) ** (k - 1) * factorial(k - 1) for k in counts)


def check(limit=8):
    totals = Counter()
    for n in range(4, limit + 1):
        for word in partitions(n):
            blocks = [tuple(i for i, a in enumerate(word) if a == j)
                      for j in range(max(word) + 1)]
            marked = []
            for block in blocks:
                if len(block) != 4:
                    continue
                a, b, c, d = block
                gaps = (tuple(range(a + 1, b)), tuple(range(b + 1, c)),
                        tuple(range(c + 1, d)), tuple(range(a)) + tuple(range(d + 1, n)))
                gap_of = {i: j for j, gap in enumerate(gaps) for i in gap}
                crossed = any(len({gap_of[i] for i in other}) > 1
                              for other in blocks if other != block)
                if crossed:
                    marked.append((block, gaps))
            if not marked:
                continue
            totals["crossed targets"] += 1
            totals["marked classes"] += len(marked)
            coefficient = 0
            for r, mobius in refinements(blocks):
                h = wins(r)
                coefficient += int(h) * mobius
                for (a, b, c, d), gaps in marked:
                    horizontal = wins(canonical((v, i in (c, d)) for i, v in enumerate(r)))
                    vertical = wins(canonical((v, i in (b, c)) for i, v in enumerate(r)))
                    overlap = (len({r[a], r[b], r[c], r[d]}) == 1 and
                               all(wins(canonical(r[i] for i in g)) for g in gaps))
                    assert (horizontal or vertical) == h, (word, r)
                    assert (horizontal and vertical) == overlap, (word, r)
                    totals["marked refinements"] += 1
                    totals["both witnesses"] += int(overlap)
            assert coefficient == 0, (word, coefficient)
    assert totals["both witnesses"] > 0
    return dict(totals)


def threshold_control():
    """Check the first possible two-class survivor, using the same raw-game oracle."""
    weights = Counter()
    for rest in combinations(range(1, 10), 4):
        left = (0,) + rest
        right = tuple(i for i in range(10) if i not in left)
        # A binary cyclic word is crossed exactly when it switches at least four times.
        if sum((i in left) != ((i - 1) % 10 in left) for i in range(10)) < 4:
            continue
        coefficient = sum(int(wins(r)) * mobius for r, mobius in refinements((left, right)))
        weights[coefficient] += 1
    return dict(weights)


if __name__ == "__main__":
    print(check())
    boundary_weights = threshold_control()
    assert boundary_weights == {0: 116, -1: 5}, boundary_weights
    print("Connected (5, 5) weights at ten positions", boundary_weights)

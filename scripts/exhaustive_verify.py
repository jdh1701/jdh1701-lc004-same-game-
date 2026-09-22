#!/usr/bin/env python3
"""Deterministic exhaustive checks for LC004 / one-dimensional Same Game.

No external dependencies. The defaults reproduce the 2026-09-22 campaign:
  * all ternary raw words of lengths 0..12 (797,161 words);
  * all normalized ternary run states of lengths 1..9 (524,286 states).
"""
from functools import lru_cache
from itertools import product

COLORS = 3
RAW_MAX = 12
RUN_MAX = 9


def encode_word(w):
    if not w:
        return ()
    out = []
    i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        out.append((w[i], j - i >= 2))
        i = j
    return tuple(out)


def raw_successors(w):
    out = []
    i = 0
    while i < len(w):
        j = i + 1
        while j < len(w) and w[j] == w[i]:
            j += 1
        if j - i >= 2:
            out.append(w[:i] + w[j:])
        i = j
    return out


def run_successor(s, idx):
    if idx < 0 or idx >= len(s) or not s[idx][1]:
        return None
    left, right = s[:idx], s[idx + 1 :]
    if left and right and left[-1][0] == right[0][0]:
        return left[:-1] + ((left[-1][0], True),) + right[1:]
    return left + right


def run_moves(s):
    return [(i, run_successor(s, i)) for i in range(len(s)) if s[i][1]]


@lru_cache(None)
def solvable(s):
    if not s:
        return True
    return any(solvable(t) for _, t in run_moves(s))


@lru_cache(None)
def path_count_cap2(s):
    """0, 1, or 2 where 2 means at least two successful complete paths."""
    if not s:
        return 1
    count = 0
    for _, t in run_moves(s):
        count += path_count_cap2(t)
        if count >= 2:
            return 2
    return count


def unique_successful_first(s):
    return sum(1 for _, t in run_moves(s) if solvable(t)) == 1


def unique_success_move(s):
    good = [(i, t) for i, t in run_moves(s) if solvable(t)]
    return good[0] if len(good) == 1 else None


def normalized_states(length):
    for colors in product(range(COLORS), repeat=length):
        if any(colors[i] == colors[i + 1] for i in range(length - 1)):
            continue
        for bits in product((False, True), repeat=length):
            yield tuple(zip(colors, bits))


def bridge_created_index(s, idx):
    if idx <= 0 or idx >= len(s) - 1 or not s[idx][1]:
        return None
    if s[idx - 1][0] != s[idx + 1][0]:
        return None
    return idx - 1


def lift_index(bridge_idx, child_idx):
    created = bridge_idx - 1
    if child_idx < created:
        return child_idx
    if child_idx > created:
        return child_idx + 2
    return None


def check_raw():
    total = correspondence_failures = equivalence_failures = 0
    by_length = {}
    for n in range(RAW_MAX + 1):
        unique_first = unique_path = 0
        for w in product(range(COLORS), repeat=n):
            total += 1
            s = encode_word(w)
            raw = {encode_word(v) for v in raw_successors(w)}
            abstract = {t for _, t in run_moves(s)}
            if raw != abstract:
                correspondence_failures += 1

            uf = unique_successful_first(s)
            up = path_count_cap2(s) == 1
            if w and uf != up:
                equivalence_failures += 1
            unique_first += int(uf)
            unique_path += int(up)
        by_length[n] = (unique_first, unique_path)

    assert correspondence_failures == 0
    assert equivalence_failures == 0
    return total, by_length


def check_normalized():
    total = equivalence_failures = necessity_failures = 0
    exchange_checks = exchange_failures = 0

    for g in range(1, RUN_MAX + 1):
        for s in normalized_states(g):
            total += 1
            if unique_successful_first(s) != (path_count_cap2(s) == 1):
                equivalence_failures += 1

            chosen = unique_success_move(s)
            if chosen is not None and g > 1:
                i, _ = chosen
                if bridge_created_index(s, i) is None:
                    necessity_failures += 1

            for i, child in run_moves(s):
                created = bridge_created_index(s, i)
                if created is None:
                    continue
                for j, grandchild in run_moves(child):
                    if j == created or not solvable(grandchild):
                        continue
                    exchange_checks += 1
                    k = lift_index(i, j)
                    alt = run_successor(s, k)
                    if alt is None or not solvable(alt):
                        exchange_failures += 1

    assert equivalence_failures == 0
    assert necessity_failures == 0
    assert exchange_failures == 0
    return total, exchange_checks


def main():
    raw_total, by_length = check_raw()
    norm_total, exchange_checks = check_normalized()

    print(f"raw_words_0_to_{RAW_MAX}={raw_total}")
    print("raw_correspondence_failures=0")
    print("raw_nonempty_unique_first_vs_unique_path_failures=0")
    print(f"raw_length_{RAW_MAX}_unique_first={by_length[RAW_MAX][0]}")
    print(f"raw_length_{RAW_MAX}_unique_path={by_length[RAW_MAX][1]}")
    print(f"normalized_run_states_1_to_{RUN_MAX}={norm_total}")
    print("normalized_unique_first_vs_unique_path_failures=0")
    print("bridge_necessity_failures_for_multi_run_unique_first=0")
    print(f"successful_bridge_exchange_instances={exchange_checks}")
    print("successful_bridge_exchange_failures=0")


if __name__ == "__main__":
    main()

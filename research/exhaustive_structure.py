#!/usr/bin/env python3
"""Exhaustive structural regression checks for LC004.

This is evidence, not a substitute for Lean proofs.  It enumerates canonical
normalized run states and checks three conjectures that guide the formal proof:

1. unique successful first choice iff exactly one complete successful path;
2. every nontrivial unique-successful-first state starts with a bridge move;
3. after a bridge move, every successful child move away from the newly merged
   run lifts to a distinct successful move in the parent.

Pinned exhaustive ranges:
  q=3 through 10 runs
  q=4 through 8 runs
  q=5 through 7 runs
"""

from functools import lru_cache
from itertools import product

State = tuple[tuple[int, bool], ...]


def canonicalize(s: State) -> State:
    labels: dict[int, int] = {}
    nxt = 0
    out = []
    for c, heavy in s:
        if c not in labels:
            labels[c] = nxt
            nxt += 1
        out.append((labels[c], bool(heavy)))
    return tuple(out)


def color_skeletons(q: int, n: int):
    """Canonical normalized color strings with at most q colors."""
    if n == 0:
        yield ()
        return

    def rec(prefix: tuple[int, ...], max_seen: int):
        if len(prefix) == n:
            yield prefix
            return
        upper = min(q - 1, max_seen + 1)
        for c in range(upper + 1):
            if prefix and c == prefix[-1]:
                continue
            if not prefix and c != 0:
                continue
            yield from rec(prefix + (c,), max(max_seen, c))

    yield from rec((), -1)


def states(q: int, n: int):
    for colors in color_skeletons(q, n):
        for bits in product((False, True), repeat=n):
            yield tuple(zip(colors, bits))


def bridge_indices(s: State) -> set[int]:
    return {
        i
        for i, (_, heavy) in enumerate(s)
        if heavy
        and 0 < i < len(s) - 1
        and s[i - 1][0] == s[i + 1][0]
    }


def legal_moves(s: State):
    out = []
    for i, (_, heavy) in enumerate(s):
        if not heavy:
            continue
        if 0 < i < len(s) - 1 and s[i - 1][0] == s[i + 1][0]:
            t = s[: i - 1] + ((s[i - 1][0], True),) + s[i + 2 :]
        else:
            t = s[:i] + s[i + 1 :]
        out.append((i, canonicalize(t)))
    return tuple(out)


@lru_cache(maxsize=None)
def solvable(s: State) -> bool:
    s = canonicalize(s)
    if not s:
        return True
    return any(solvable(t) for _, t in legal_moves(s))


@lru_cache(maxsize=None)
def path_count(s: State) -> int:
    s = canonicalize(s)
    if not s:
        return 1
    return sum(path_count(t) for _, t in legal_moves(s))


def successful_moves(s: State):
    return tuple((i, t) for i, t in legal_moves(s) if solvable(t))


def run_range(q: int, max_runs: int):
    rows = []
    exchange_cases = 0

    for n in range(1, max_runs + 1):
        total = solved = unique_first = unique_path = 0
        for s in states(q, n):
            total += 1
            successful = successful_moves(s)
            paths = path_count(s)

            solved += int(solvable(s))
            unique_first += int(len(successful) == 1)
            unique_path += int(paths == 1)

            assert (len(successful) == 1) == (paths == 1), (
                "unique-first/unique-path counterexample",
                s,
                successful,
                paths,
            )

            if len(successful) == 1:
                i, _ = successful[0]
                assert n % 2 == 1 and i == n // 2, (
                    "center-run counterexample",
                    s,
                    successful,
                    paths,
                )
                if len(s) > 1:
                    assert i in bridge_indices(s), (
                        "bridge-necessity counterexample",
                        s,
                        successful,
                        paths,
                    )

            for i, child in legal_moves(s):
                if i not in bridge_indices(s):
                    continue
                merged_child_index = i - 1
                for j, _ in successful_moves(child):
                    if j == merged_child_index:
                        continue
                    lifted = j if j < merged_child_index else j + 2
                    parent_success = dict(legal_moves(s)).get(lifted)
                    exchange_cases += 1
                    assert parent_success is not None and solvable(parent_success), (
                        "bridge-exchange counterexample",
                        s,
                        i,
                        child,
                        j,
                        lifted,
                        parent_success,
                    )

        rows.append((n, total, solved, unique_first, unique_path))

    return rows, exchange_cases


def main():
    ranges = ((3, 10), (4, 8), (5, 7))
    total_states = 0
    total_exchange = 0
    total_unique_first = 0
    for q, max_runs in ranges:
        rows, exchange = run_range(q, max_runs)
        total_states += sum(row[1] for row in rows)
        total_exchange += exchange
        total_unique_first += sum(row[3] for row in rows)
        print(f"q={q}, through {max_runs} runs")
        for row in rows:
            print("  runs=%d states=%d solvable=%d unique_first=%d unique_path=%d" % row)
        print(f"  bridge_exchange_cases={exchange}")

    assert total_states == 489_538, total_states
    assert total_exchange == 1_163_048, total_exchange
    assert total_unique_first == 1_002, total_unique_first
    print(
        f"PASS states={total_states} unique_first={total_unique_first} "
        f"bridge_exchange_cases={total_exchange}"
    )


if __name__ == "__main__":
    main()

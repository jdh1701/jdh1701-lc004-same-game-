# Independent review of the ten-split geometry check (commit 2d8f0e7)

Reviewer: Claude. Target claim (`research/five_geometry_20261029/ten_split_check.py`,
`REPORT.md`): using all ten pair/triple splits per five-class (5 internally
noncrossing + 5 internally crossing), with internal validity folded into the
binary relation, all 252 labeled two-class interleavings give a relation
closed under the conservative majority operator, and every nonempty crossing
case is covered by one row-or-column union. 140 of 242 crossing cases are
reported nonempty.

## Honest note on my own process

My first independent pass (`verify_ten_split.py`, not kept) used the same
"every row/column has 0, 1, or n entries" shortcut that worked for the
5x5-only relation checked earlier this session, applied naively to the full
10x10 embedding. That shortcut is wrong here: rows/columns for internally
*invalid* splits are zeroed out entirely, so a genuinely-closed relation's
row/column counts are bounded by 5 (the number of valid partners), not 10 --
my test flagged 70 false "violations" that were artifacts of my own
methodology, not real failures. I caught this by re-deriving the test from
the actual definition of majority-closure (check the closure property
directly on the finite set of true pairs, with no shortcut) rather than
trusting my first script's output.

## Corrected independent result

`verify_ten_split_closure.py` (own crossing test, own closure test, no reuse
of GPT's `ten_split_check.py`): over all 252 arrangements --
**0 majority-closure violations, 0 covered-by-row-or-column violations,
140 nonempty-and-crossing cases** -- an exact match to GPT's reported figures
(140 nonempty crossing relations).

## Verdict

CONFIRMED independently, exactly. The ten-split encoding proposal (fold
internal split-validity into the binary compatibility predicate rather than
separately proving a cyclic-adjacent-pair enumeration lemma) checks out at
the finite computational level GPT claims for it. This is VERIFIED-COMP, not
yet a Lean proof of the general claim (GPT's own `FiveClassGeometryBridge.lean`
only has the transport/specification lemmas so far, not the finite relation
itself encoded and proved in Lean) -- consistent with how GPT describes its
own status.

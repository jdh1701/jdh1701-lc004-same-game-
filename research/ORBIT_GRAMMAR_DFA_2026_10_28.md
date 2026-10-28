# Color-symmetry quotient of the direct CFG counting machine (2026-10-28)

## Exact method
The parser-set automaton of DIRECT_GRAMMAR_DETERMINIZATION_2026_10_28.md accepts one deterministic path per DISTINCT word of fixed length n. The candidate grammar and parser transitions commute with any global permutation of q color names. Thus states in the same permutation orbit have equivalent future behavior up to relabeling.

Canonicalize each reachable parser-set state by lexicographically minimizing the SORTED collection of its stacks over all q! permutations. Count prefix transitions with multiplicity rather than enumerating prefixes; one representative stands for all symmetry-equivalent states. This is standard group-action reduction; no originality/novelty claim by itself.

## Executed exact results
q=3,n=12, unquotiented peak states 1419, color-orbit peak 239, count 71385 both ways. Unquotiented runtime 0.933 s, orbit 0.532 s.
q=3,n=14, unquotiented peak states 5634, color-orbit peak 941, count 657849 both ways. Unquotiented runtime 7.22 s, orbit 3.45 s.
q=3,n=15, color-orbit peak 2247, count 2003151, runtime 10.879 s. The count agrees with OEIS A035617.
q=3,n=16 attempt exceeded local execution time budget. NO count reported and no claim of scalability beyond these tested cases.

For q=3,n=12, orbit-state counts by prefix depth:
1, 1, 2, 5, 14, 41, 122, 211, 239, 192, 59, 6, 1.
For q=3,n=14:
1, 1, 2, 5, 14, 41, 122, 364, 702, 941, 932, 571, 78, 6, 1.

## Adversarial check
A first implementation incorrectly used Python's min on frozensets (subset partial order) and produced NO symmetry reduction, despite correct counts. Fixed by comparing sorted tuples lexicographically. This failure is retained as an implementation lesson.

## Verification and limitations
Original Game ↔ grammar equivalence remains generally unproved. This is exact for the grammar by direct deterministic parse-state construction. Independent full original-game comparisons pass q=2 through n=10, q=3 through n=10 and q=4 through n=8. State growth is still significant and orbit canonicalization costs up to q!; this is NOT a solution to the published q>=3 enumeration problem.
Next: equivariant transition proof in Lean, dynamic orbit canonicalization without factorial q!, and extrapolation-resistant complexity benchmarking.

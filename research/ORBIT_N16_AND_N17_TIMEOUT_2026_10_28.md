# Same Game direct grammar determinization: length-16 extension and attempted length 17
Date: 2026-10-28

## Actually executed local commands and raw output
python same_game_orbit_dfa.py --q 3 --n 16
last levels:
 13 1536 804093
 14 94 1830627
 15 6 3808425
 16 1 6103743
FINAL {'q': 3, 'n': 16, 'count': 6103743,
'levels': [1,1,2,5,14,41,122,365,1090,2307,3551,4219,3608,1536,94,6,1],
'edges': 49048, 'closures': 20083, 'orbit_canonical_states': 20083,
'seconds': 33.198}

This EXACT grammar-language count matches established OEIS A035617, and is not a novel sequence term. Three-color word space at length 16 has 3^16 = 43,046,721 possibilities; our bounded parser builds 4,219 orbit states at peak, but the parser configurations inside each state are not counted in the state total and complexity is not established polynomial.

python same_game_orbit_dfa.py --q 3 --n 17
The computation was interrupted after a 180-second timeout; it reported depth counts up to depth 9, then NO FINAL VALUE. No success, no extrapolated count. This is a negative scaling result and an important limit.

## Mathematical and Lean objective
Color-permutation symmetry of grammar membership has already been Lean-verified. The current PR adds the corresponding step/path equivariance for auxiliary pair/triple erasure; this theorem is related to correctness of group-orbit quotient but DOES NOT itself formally verify the Python deterministic automaton or prove original Same Game <-> grammar equivalence.

## Updated strategy
A. Keep building symbolic, determinized, distinct-word counters with honest memory/time tracking and held-out checks.
B. Attack performance bottleneck (closure computation and parser-state canonicalization) on n=17 with profiling, without claiming polynomial complexity.
C. Derive a compressed recurrence over orbit states or a new invariant that avoids constructing those states explicitly. If no compression theorem survives, record the null result.
D. Prove raw-game equivalence to grammar in Lean; a correct grammar counter alone cannot resolve the original mathematical problem.
E. Compare precise claims to Kurz (2001) and Burns/Purcell (2007). Standard pushdown determinization and color group actions are NOT alone bibliographically novel.

No claim that the open general q>=3 enumeration problem is solved.

# Canonical parse research cycle — 2026-10-28

Status: computational checks completed; no new Lean build; no claim of bibliographic novelty.

For the ambiguous grammar S -> ε | a S a S | a S a S a S, define a deterministic canonical parse of each accepted word by recursively selecting the lexicographically least valid binary/ternary production and canonical child parses. A substring dynamic program recognizes the grammar in O(n^4) time with O(n^2) boolean chart cells; canonical certificate comparisons require additional care.

The minimal failure of unique root pair decomposition is 0000: binary-root split positions 1 and 3 are both valid. Canonicalization therefore must select, rather than assume, a unique split.

Independent Python exhaustive comparisons of maximal-run winning vs grammar-derivation existence for every 3-color word length 2..11 showed zero disagreements. Winning, uniquely parsed, ambiguous, total derivations:
2: 3,3,0,3
3: 3,3,0,3
4: 15,12,3,18
5: 33,30,3,45
6: 105,66,39,162
7: 297,210,87,567
8: 879,480,399,1890
9: 2631,1386,1245,7128
10: 7833,3600,4233,24786
11: 23697,9636,14061,93555

Proof obligations:
(1) grammar iff adjacent pair/triple reductions,
(2) pair/triple reductions iff maximal-run Same Game,
(3) canonical parser correctness,
(4) compressed distinct-word counting rather than enumerating each accepted word.

The canonical parse is unique by construction, but this DOES NOT produce a closed-form enumeration of distinct winning words. Lean was not available locally; these new obligations were not Lean-certified. Reference: https://oeis.org/A035617

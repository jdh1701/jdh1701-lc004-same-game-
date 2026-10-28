# Exact residual automata for Same Game (2026-10-28)

Status: freshly executed Python enumeration; NOT Lean-verified. A standard automata-minimization construction, not a claim of novel mathematical theory.

For target length n and prefix p, define residual R_n(p)={s: |ps|=n and ps is winnable}. Equate prefixes of the same length if their residuals agree. Bottom-up trie minimization on winning words creates a deterministic DAG with one accepting path per distinct word, eliminating grammar-derivation overcounts.

q=3: columns n / winning words / trie nodes / minimal live states:
4 / 15 / 43 / 15
5 / 33 / 88 / 33
6 / 105 / 295 / 72
7 / 297 / 748 / 145
8 / 879 / 2281 / 289
9 / 2631 / 6376 / 628
10 / 7833 / 18985 / 1183
11 / 23697 / 55270 / 2662
12 / 71385 / 164455 / 4855

Spot checks q=2 n=10: 602 winning /150 states; n=12: 2774 /300; q=4 n=8: 3100 /793; n=9: 10876 /2168.

Proof: induct on remaining length. The residual accepted by a trie node is a disjoint union of first-letter-prefixed residuals of its children. Therefore nodes have identical residuals iff their labeled child residual maps agree. Interning equal maps merges exactly equivalent states. Counting paths in the DAG recovers the exact number of distinct winning words.

CAVEAT: the DAG here was constructed only AFTER exhaustive generation of all winning words. It therefore does not solve the general enumeration problem or establish a fast direct counting recurrence. Next target is to derive and certify residual-state transitions without first enumerating every winning word. Lean was not run in this cycle. Source program is same_game_residual_automata.py in project artifacts.

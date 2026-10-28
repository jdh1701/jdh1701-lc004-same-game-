# Same Game: grammar derivation-count research, 2026-10-28

Status: independent mathematical derivation plus Python checks; NOT Lean-certified, and no claim of bibliographic novelty.

For grammar S -> epsilon | a S a S | a S a S a S, where each production uses one identical letter a, let D_n(q) count parse-tree derivations of words of length n over q colors. This is not the number of distinct winning words.

Generating function: D(x,q) = 1 + q*x^2*D(x,q)^2 + q*x^3*D(x,q)^3.

Exact coefficient:
D_n(q) = sum over a,b>=0 with 2a+3b=n of n!/(a! b! (a+2b+1)!) * q^(a+b).

Proof: derivations correspond to ordered rooted trees with a binary and b ternary internal nodes, and a+2b+1 leaves. Standard plane-tree enumeration gives the factorial coefficient. Each internal node chooses one of q colors.

Python exhaustive cross-check with three separate predicates: (1) maximal-run Same Game wins, (2) arbitrary adjacent pair/triple reductions, (3) existence of a grammar derivation. Zero disagreements for every ternary word length 2 through 11.

n | winning distinct words | unique-derivation winning words | ambiguous winning words | total derivations
2 | 3 | 3 | 0 | 3
3 | 3 | 3 | 0 | 3
4 | 15 | 12 | 3 | 18
5 | 33 | 30 | 3 | 45
6 | 105 | 66 | 39 | 162
7 | 297 | 210 | 87 | 567
8 | 879 | 480 | 399 | 1890
9 | 2631 | 1386 | 1245 | 7128
10 | 7833 | 3600 | 4233 | 24786
11 | 23697 | 9636 | 14061 | 93555

At n=11, 14,061 of 23,697 winning ternary words are multiply derived, demonstrating substantial overcount. OEIS A035617 confirms winning counts: https://oeis.org/A035617 .

Critical proof gaps:
1. Prove maximal-run deletion iff pair/triple-deletion semantics for every finite word.
2. Prove that grammar recognizes the pair/triple-deletion language.
3. Find a canonical, non-overcounting decomposition of distinct winning words. Leftmost-greedy is false (00110 is a counterexample).
4. Run proofs in Lean and inspect axioms. No new Lean execution was possible during this cycle.

The formula for D_n(q) is a theorem about parse trees, not a solution of the open q>=3 distinct-string counting problem.

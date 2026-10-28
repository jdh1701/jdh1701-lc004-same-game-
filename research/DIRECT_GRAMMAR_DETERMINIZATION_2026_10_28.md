# Direct distinct-word counting through bounded CFG determinization
Date: 2026-10-28
Status: NEW ALGORITHM IMPLEMENTED AND TESTED, NOT A SOLUTION TO THE OPEN GENERAL ENUMERATION PROBLEM, NOT LEAN-CERTIFIED.

## Idea
The grammar G: S -> ε | a S a S | a S a S a S, a in an alphabet of q colors, is ambiguous. Counting its derivations overcounts distinct words.

For fixed target length n, represent all reachable nondeterministic parser stacks after a prefix as a SINGLE deterministic state: a frozenset of stacks. A stack contains literal colors or nonterminal S. Closure removes a leading S by ε, or expands it into a pair or triple production. Prune stacks with more pending literal symbols than remaining input length. A transition consumes one leading literal matching the next color and takes closure. Aggregate counts of DISTINCT prefixes for identical deterministic states. At depth n, sum counts of states containing an empty stack. Because the process is deterministic on each input word, each accepted word contributes exactly once.

This directly builds the reachable deterministic states from production rules and does NOT generate all q^n words or first enumerate all winners. It is a bounded-depth powerset construction for a context-free language, a standard technique; no novelty is claimed for determinization itself. Its applicability to this Same Game grammar and compression statistics are concrete research observations.

## Executed results
q=3,n=8: 879 distinct accepted, peak states 105, 312 distinct closures, 0.013 s.
q=3,n=12: 71,385 accepted, peak states 1,419, 5,219 distinct closures, 0.933 s.
q=3,n=14: 657,849 accepted, peak states 5,634, 22,502 closures, 7.22 s.
q=4,n=10: 39,244 accepted, 4,855 closures, 0.47 s.

One q=3,n=16 run exceeded the configured execution timeout; count UNAVAILABLE, not presumed. State-space growth remains a major limitation and the algorithm is not established as polynomial-time.

## Independent validation
Compared aggregate grammar-accepted counts against an independent recursive maximal-run Same Game solver for:
- q=2, all lengths 0..10
- q=3, all lengths 0..10
- q=4, all lengths 0..8
ALL checked pairs agreed. This validates those finite cases; it does NOT establish the grammar <-> maximal-run equivalence universally.

## What is actually established
For any fixed q,n, the program computes the number of distinct words of length n accepted by the displayed grammar, provided sufficient execution resources. The count is not a tally of parse-tree derivations. The correctness invariant is: at depth d each deterministic parser state is the set of all viable nondeterministic grammar stacks reachable after a given d-character prefix, with exactly one deterministic trajectory for each word. Aggregating prefix counts over identical states thus counts every accepted word once.

## Next discriminating experiments
1. Compare memory/state growth for n=14,15,16 vs naive q^n enumeration using fixed resource budgets; avoid selecting only successes.
2. Symbolically quotient by global color-renaming permutations, then expand with falling-factorial weights; prove transitions respect renaming.
3. Attempt residual-state minimization DURING construction, not afterward; find canonical signature without enumerating words.
4. Derive a recurrence or finite algebraic equation for reachable state counts that avoids full powerset expansion.
5. Complete Lean grammar <-> actual raw-game semantics equivalence. Without this bridge, algorithm is exact for the proposed grammar, not proved exact for all Same Game positions.

## Why this is closer to the research goal
Earlier grammar generating function counts derivations, and earlier trie minimization needed all winners in advance. This algorithm directly counts DISTINCT grammar words through compact state aggregation. It still does NOT settle the published q>=3 general enumeration problem, nor demonstrate publication novelty.

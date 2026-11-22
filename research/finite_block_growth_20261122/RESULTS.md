# Follow-up to the finite-block criterion

Lean 4.19.0 checked two further results. The axiom report for both uses propext, Classical.choice and Quot.sound.

* ProperBlock.lean proves that the number of length-(2H+1) ternary words with distinct neighbors is exactly 3·2^(2H). Every one of them is forbidden between stack endpoints of height at most H. On m aligned blocks the fraction surviving this necessary condition is at most (1-(2/3)^(2H))^m. Arbitrary intermediate heights within blocks are allowed.
* SparseRepair.lean proves full ternary growth under an integer certificate condition. For every positive scale m it suffices to find one length n, terminal height k and budget d such that k+2 ≤ d, m·d ≤ n and 3^n ≤ 2^d · card(Short n k). Here Short counts distinct labeled inputs that admit at least one residual of height ≤ k. The Lean quantifier includes m=0, which follows from any positive-scale witness.

After the three sources in the first README have been copied to the project root, copy these two modules alongside them. Using the same temporary olean directory, run

    lake env bash -c 'export LEAN_PATH="$LEAN_PATH:/tmp/lc004-block"; lean -o /tmp/lc004-block/FiniteBlock.olean FiniteBlock.lean && lean ProperBlock.lean && lean SparseRepair.lean'

## Finite check of the sparse condition

Run from this research directory:

    python3 witness.py | diff sparse-witnesses.txt -

The Python program counts distinct words accepted with a stack capped throughout. Its deterministic states are sets of literal stacks. It starts at the singleton containing the empty stack and retains the counts of words ending in a state containing the empty stack. The program checks conservation of total word count at every length. As a separate small test it compares every length-six word at each of the four caps with a direct recursive evaluator.

For lengths 1 through 320 it maximizes n/d with terminal height k=0, requiring d ≥ 2. A cap of 4 gives n=314 and d=24, enough for every integer scale m from 0 through 13. The computation uses integer arithmetic. The individual large count was generated in Python and has not been replayed in Lean. A family for unbounded m is still missing. These finite checks do not improve the project's existing growth-rate lower bound.

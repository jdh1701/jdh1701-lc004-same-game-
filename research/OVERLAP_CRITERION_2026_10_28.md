# Overlap criterion: a sharper second-diagonal theorem target
Date 2026-10-28

## New independently executed adversarial test
For each k=2,...,7, generate every noncrossing perfect matching on 2k+2 positions, merge every choice of two pairs into one color, and canonicalize colors. Count the number of representations of each resulting word. Independently test whether its ORIGINAL color partition (one 4-block and k-1 2-blocks) is noncrossing, using the alternating-indices crossing criterion.

RESULT:
k=2: 9 distinct; 6 doubly represented; 0 criterion failures.
k=3: 56 distinct; 28 doubly represented; 0 failures.
k=4: 300 distinct; 120 doubly represented; 0 failures.
k=5: 1485 distinct; 495 doubly represented; 0 failures.
k=6: 7007 distinct; 2002 doubly represented; 0 failures.
k=7: 32032 distinct; 8008 doubly represented; 0 failures.

The count of doubly represented words equals binom(2k+2,k-1) for all checked k. Each generated word has exactly one or two representations, never three or more.

## General proof plan, not yet completed
A 4-block with ordered positions a<b<c<d has exactly two noncrossing internal pairings: (a,b),(c,d) and (a,d),(b,c). The crossing pairing (a,c),(b,d) is excluded. All other colors occur exactly twice and have forced pairs. Thus a word has at most two representations. It has both iff neither internal pairing crosses any forced other-color pair. Conjecture: this happens iff the ORIGINAL partition with the 4-block is noncrossing. Establish this via a complete classification of the five intervals cut by a,b,c,d; in particular rule out forced pairs that cross the 4-block but somehow avoid both internal pairings. A general proof would establish the exact overlap multiplicity.

Standard noncrossing partition enumeration with one 4-block and k-1 pair blocks gives (2k+2)!/((k+3)!(k-1)!)=binom(2k+2,k-1). Combined with Catalan(k+1)*choose(k+1,2) pair-merge representations, this gives the four-occurrence formula.

## Crucial separate completeness issue
The formula counts the union of noncrossing pair-merge representations. Proving it equals ALL maximal-run-winning words of profile (4,2,...,2) requires the general game-history-to-noncrossing-decomposition lemma. The overlap test does not prove that completeness. Likewise the two-triple noncrossing count requires the same characterization.

## Verification status
Executed independent Python checker locally and committed source. This is computational evidence, NOT Lean kernel verification or a bibliographic novelty claim. Next: formalize overlap iff noncrossing, then the game-history characterization.

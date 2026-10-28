# Same Game: second-from-maximal-color diagonal, conjectured exact formula
Date 2026-10-28. STATUS: plausible combinatorial derivation and checked numerical predictions, NOT Lean-verified or bibliographically novel.

## Statement
Let a(n,k) count winning restricted-growth color patterns of length n using exactly k colors. For n=2k+2 (k>=2), propose:

a(2k+2,k) = choose(k+1,2)*Catalan(k+1) - choose(2k+2,k-1)
            + (2k+2)! / [2*(k-2)!*(k+3)!].

The first two terms count patterns with one color appearing 4 times and the others twice. The final term counts patterns with two colors appearing 3 times and all others twice.

## Why only two multiplicity profiles?
Every color in a winning word must occur >=2 times. Since n-2k=2, the nonnegative excess multiplicities sum to two. Thus only (4,2,...,2) and (3,3,2,...,2) occur.

## Combinatorial explanation to formalize
Profile (3,3,2,...): each color can be removed only in one operation (the 3-block may be deleted whole); a winning history induces a noncrossing partition of positions with two triple blocks and k-2 pairs. Conversely a noncrossing partition of these sizes yields an innermost removable block. Standard plane-tree noncrossing partition enumeration gives n!/[2!(k-2)!(k+3)!].

Profile (4,2,...): a successful history induces a noncrossing perfect matching after splitting the four-occurrence color into two pairs, possibly splitting a single deletion of length four. Choose a noncrossing perfect matching on 2k+2 positions (Catalan(k+1)) and choose two of its k+1 pairs to merge into one color (choose(k+1,2)). A word may have two such matchings when its original four-block is itself noncrossing relative to the other blocks. The number of these doubly represented words is choose(2k+2,k-1). This last exact overlap characterization is the CRITICAL PROOF OBLIGATION; it must be established with an explicit matching classification, not inferred solely from numerical agreement.

## Independent numerical checks
Previously computed RGS grammar coefficients:
k=2 n=6: 9+3=12 (observed 12).
k=3 n=8: 56+28=84 (observed 84).
k=4 n=10: 300+180=480 (observed 480).
k=5 n=12: 1485+990=2475 (observed 2475).
k=6 n=14: 7007+5005=12012 (observed 12012).

Held-out predictions NOT independently tested:
k=7 n=16: 32032+24024=56056.
k=8 n=18: 143208+111384=254592.
No novelty claim until checking primary literature including Kurz and Burns/Purcell.

## Strategic significance
This is a meaningful general near-maximal-color formula candidate, unlike fitting an arbitrary recurrence. It reduces a whole infinite family to a specific noncrossing matching overlap lemma. It does NOT resolve all n,k and therefore does NOT solve general Same Game enumeration.

## Falsification
Compute a(16,7) independently from the RGS parser, ideally with a profile-specific solver instead of full Q=8 determinization; compare to 56056. Also prove the overlap correction bijection. If mismatch, retract formula and retain only the verified decomposition of multiplicity profiles.

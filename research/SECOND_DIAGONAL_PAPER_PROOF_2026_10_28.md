# Second-diagonal Same Game formula: combinatorial proof architecture and Lean-certified local overlap lemma
Date: 2026-10-28

## Precise result
For k>=2, a(2k+2,k) counts distinct *winning* color-isomorphism patterns using exactly k colors. A candidate exact formula is
  binom(k+1,2)*Catalan(k+1) - binom(2k+2,k-1)
  + (2k+2)!/(2*(k-2)!*(k+3)!).

## Proof roadmap and justified mathematical reductions
Every color in a winning word has at least two occurrences. An n=2k+2 winning word therefore has only two possible multiplicity profiles: one fourfold and k-1 pairs, or two triples and k-2 pairs.

A complete successful deletion history can be decomposed into blocks of size 2 or 3. For these restricted profiles, a paired color can only be deleted as one pair. A color appearing three times must be deleted as one triple (otherwise its remaining singleton can never be removed). A color appearing four times must be deleted either once as a full group of four (refine into two adjacent pairs) or twice as pairs. Reverse the deletion history: the resulting pair/triple chunks are inserted into consecutive positions of the CURRENT word. The induced blocks on original positions form a noncrossing partition, because insertion at a gap can only nest previously inserted blocks, never interleave them. A full group of four can be refined into two adjacent pair chunks without introducing a crossing.

Conversely, any noncrossing pair/triple partition into monochromatic blocks can be reduced in the auxiliary pair/triple system by deleting an innermost block and recursing. To obtain a winning history for the ORIGINAL maximal-run game requires the insertion-closure / auxiliary-to-raw lifting theorem, argued mathematically in prior research but NOT fully proved in Lean for raw words. This is a formalization gap, not a license to assert an end-to-end Lean proof.

## Fourfold profile exact counting
A noncrossing perfect matching on 2k+2 positions has Catalan(k+1) choices. Choose two of the k+1 pairs to assign the same color, producing binom(k+1,2)*Catalan(k+1) matching-with-merge representations. Every fourfold-profile winning word has at least one such representation by the history decomposition above. The four occurrences a<b<c<d admit exactly TWO noncrossing internal pairings: (a,b)(c,d) and (a,d)(b,c). The third pairing (a,c)(b,d) crosses.

All other color pairs are forced and mutually noncrossing. Both internal pairing choices are compatible with ALL forced pairs iff no forced pair crosses the original four-block. In other words, a word has two representations iff the ORIGINAL partition is noncrossing. A formal local geometric crossing criterion for one external pair was Lean-verified in LC004.FourBlockCrossing.lean; LC004.FourBlockOverlapCorollary.lean submits the logical negation/compatibility corollary.

Count the double representations using the standard block-size refined noncrossing-partition formula:
  NC_n(m_1,m_2,...) = n! / ((n+1-B)! * product_i m_i!),
where B = total number of blocks, and m_i is the number of blocks of size i. With n=2k+2, B=k, m_4=1, m_2=k-1:
  (2k+2)! / ((k+3)!(k-1)!) = binom(2k+2,k-1).
Subtract this overlap once.

## Two triple profile
Each color is deleted once, and a winning history induces a noncrossing partition with m_3=2 and m_2=k-2. The same refined partition formula gives:
 (2k+2)!/[2!(k-2)!(k+3)!].

## Scope and provenance
This forms a candidate rigorous *paper proof* of the second-diagonal formula contingent on carefully formalizing the deletion-history/noncrossing correspondence and raw-game lifting. It is NOT a full Lean-verified second-diagonal theorem and not a solution to all n,k enumeration. Standard noncrossing partitions and the refined-count formula are classical; bibliographic originality of this particular Same Game diagonal remains unverified. Prior literature: Sascha Kurz (2001) Polynomials in same game, Burns & Purcell (2007).

## Tests
Exhaustive independent matching representation and crossing classification checks k=2..7 passed, including n=16 k=7: 32,032 fourfold patterns, 8,008 doubles, 24,024 two-triple patterns, total 56,056. These are not substitutes for the universal proof.

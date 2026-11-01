# Finite horizons and reversal-averaged enumeration

This advances LC004/A035617; it does not solve the all-length scalar enumeration problem. Lean horizon proofs are submitted for checking. The reversal-averaging argument below is a paper proof, separately tested computationally.

## Formal horizon obligations

LC004/FusionHorizon.lean proves a stack-length bound for every fusion computation. It implies that stacks longer than the remaining word length cannot accept. Removing them preserves the original-game indicator for every continuation within the horizon.

It also proves the converse separation statement: for finite sets S,T of proper stacks, their truncations to length at most r coincide iff they accept exactly the same continuation words of length at most r. This is a theorem about individual continuation words, not averaged counts or words of exactly length r.

## Reversal preserves average counts, not transition classes

For a finite set S of proper words let P_S=sum_{s in S} X_s, in the noncommutative algebra with X_a^2=1+X_a. Coefficients are nonnegative integers. Let tau take the coefficient of the empty word, and let * reverse every monomial. Define

    F_r(S) = sum_{|w|=r} 1[tau(P_S X_w)>0].

The prior global fusion theorem identifies this indicator with acceptance from S, using the matching stack orientation. The implemented tuples are top-last; reversing this convention changes neither the algebra nor the invariance conclusion.

Here are the algebraic obligations rather than an assumption of cyclicity:

1. The proper words form a normal-form basis. Reduce aa to 1+a. Degree decreases. Disjoint reductions commute; the only overlapping ambiguity aaa reduces in either order to 1+2a. Resolving the first two reductions and inducting on degree gives the same normal form for every reduction order. Multiplication is associative, coefficients are nonnegative, and reversal is an anti-automorphism because the relations are reversal invariant.
2. For proper u,v, tau(X_u X_v)=1 if v=reverse(u), and is zero otherwise. Reading u from empty has one computation. A proper continuation can accept only by popping at every step, as proved in FusionStack.lean. Thus the accepting path is unique, not just nonempty.
3. Expanding in that basis gives tau(AB)=tau(BA), and tau(A*)=tau(A), for all finite polynomials A,B.

Consequently

    tau(P_(S*) X_w) = tau((P_(S*) X_w)*)
                       = tau(X_(reverse(w)) P_S)
                       = tau(P_S X_(reverse(w))).

Reversal permutes all words of length r, so F_r(S*)=F_r(S) for every r and every finite S. A global permutation of colors also preserves F_r by a bijection on future words. Trimming long stacks commutes with reversal and preserves F_r when the trim bound is r.

The orientation detail can be checked directly: for top-first stack s the algebra polynomial is X_(reverse(s)); for top-last stack s it is X_s. The implemented test uses top-last stacks. Its accepting coefficient is exactly tau(P_S X_w).

## Why repeated replacement gives an exact counting algorithm

The ordinary recurrence is F_(r+1)(S)=sum_a F_r(step(S,a)). After every step we may trim to length r and replace the support by any representative under common color permutations and reversal of all stacks. Both operations preserve F_r. Induction therefore proves the modified recurrence has the same answer for every remaining length.

Equivalently, the weighted sum of F_remaining across the current states is invariant as a layer is expanded. This proof does NOT require the quotient to preserve its outgoing transition multiset. In fact it does not: the support of 001 and its reversed support have different multisets of successor classes, recorded explicitly in checks.json. A proof that merely calls reversal a transition automorphism would be wrong. Nor do we claim each state weight is the number of original prefixes with that actual support; it is a weight in an equivalent counting recurrence.

The new C++ counter extends the prior forward DP with this representative choice. It remains an expanding finite-state computation, not a fixed-size transfer matrix or scalar closed formula.

## Checks and provenance

The Python implementation separately checks counts through N=14 and the C++ version through N=20. Tests include all 1024 subsets of the ten proper ternary stacks of length at most two, with every continuation of length at most five; 9841 word/reversal support identities; and proper-basis trace pairings. The first failure of strong transition lumpability is recorded rather than hidden.

PR52 remains green at source 293cdb9766aa386963f59e33db54d43c48317171: 250 modules and 4266 declarations audited. PR35 advanced to ecb6dcd5 with a concrete re-enumeration of the prior (5,5,7) counterexample: coefficient +1, seven certificates, NCConnected. Its algorithm uses targeted class decompositions and the same signed-join recurrence; this is additional computational corroboration, not a new general theorem or independent verification of every prior proof. It adds no Lean source.

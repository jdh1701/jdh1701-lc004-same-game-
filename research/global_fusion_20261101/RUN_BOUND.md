# A run-normalized algebraic majorant

**PAPER PROOF + finite exact checks; not Lean formalized. Not an enumeration formula for winning words.**

Let W_b(n) count winning words over b colors. The Boolean fusion bridge implies that replacing each maximal run a^k by X_a when k=1, or by I+X_a when k>=2, preserves support. Indeed X_a^2=I+X_a and every higher power has the same two-term positive support. Work over nonnegative integers after this replacement. The empty-stack coefficient c(w) is a nonnegative integer with c(w)>0 exactly when w wins, so W_b(n)<=A_b(n):=sum_{|w|=n}c(w).

Unlike the unrestricted fusion multiplicity, this does not count the redundant ways to reduce a single long run. It is still not unambiguous: c(aabbaa)=2.

## Deriving the series

Let T=sum_a X_a on the basis of proper stacks, with empty vector e. Then X_a^2=I+X_a, and

    M_b(z) = <e,(I-zT)^(-1)e> = 1/(1-b z^2 F_b(z)),
    F_b(z) = 1 + z F_b(z) + (b-1) z^2 F_b(z)^2.

The root has b outward neighbors and no loop. Every other vertex has one parent, b-1 children and one loop; first-return decomposition gives these two equations. All series take their branch with constant term 1.

A maximal run of color a contributes

    R_a(z) = z X_a + z^2/(1-z) (I+X_a)
           = beta I + alpha X_a,
    alpha=z/(1-z), beta=z^2/(1-z).

Only sequences of runs with unequal adjacent colors are allowed. The noncommutative run identity is

    S(R_1,...,R_b) = (I - sum_a R_a(I+R_a)^(-1))^(-1).

To verify it, let S_a be the sum of nonempty run products starting with color a. Then S_a=R_a(S-S_a), so S_a=(I+R_a)^(-1)R_a S. Summing S=I+sum S_a proves the identity formally; no commutativity between different colors is assumed.

Direct multiplication using X_a^2=I+X_a gives

    R_a(I+R_a)^(-1) = (z^4 I + z(1-z) X_a)/P(z),
    P(z)=1-z+z^2-z^3+z^4.

Set Q_b(z)=P(z)-b z^4. Taking the empty coefficient yields the exact algebraic majorant

    A_b(z) = P(z)/Q_b(z) * M_b(z(1-z)/Q_b(z)).

This is a formula for sum c(w), not for W_b(n). In three colors its coefficients start 1,0,3,3,15,33,111,315,1005,3111, whereas the winning counts already differ at n=6.

## Explicit exponential bound for five colors

For b>=2 put lambda=1+2 sqrt(b-1) and h(s)=(b-1)^(-|s|/2). At a nonroot stack, (Th)(s)/h(s)=lambda. At the root it is b/sqrt(b-1)<=lambda. Positivity gives (T^n h)(e)<=lambda^n, and since the contribution of e alone is M_b(n), M_b(n)<=lambda^n. Thus M_b(x)<=1/(1-lambda x) for 0<=x<1/lambda.

For b=5, lambda=5. Put r=41/200. On [0,r],

    g(z)=Q_5(z)-5z(1-z)=1-6z+6z^2-z^3-4z^4

is decreasing: g'(z)=-6+12z-3z^2-16z^3<0. Its endpoint value is

    g(r)=2588189/400000000 > 0.

Consequently Q_5(z)>0 and 0<=z(1-z)/Q_5(z)<1/5 on this interval. The displayed algebraic expression for A_5 therefore extends analytically along the entire interval and a little beyond its right endpoint. Since A_5 has nonnegative Taylor coefficients, its radius cannot end inside this interval: the nonnegative-coefficient singularity theorem (Pringsheim) would require a singularity at that positive real radius. It follows that the series converges at r. The preceding positive bound gives

    A_5(r) <= P(r)/g(r)
           = 1328281561/10352756 < 129.

Termwise nonnegativity now proves, for every n>=0,

    W_5(n)/5^n <= 129 (40/41)^n.

For b>=6 the earlier unnormalized bound already gives exponential decay, since 1+2 sqrt(b-1)<b. Thus exponential decay is established here for every b>=5. No analogous conclusion for b=3 or b=4 follows from this majorant, and no novelty claim is made without a broader literature review.

## Independent checks and one tempting failure

run_bound.py exhaustively compares capped-run support with full fusion support for binary words through length 10, ternary through length 9, and four colors through length 7. It independently expands the formula using integer power-series arithmetic and compares all the resulting coefficients. The five-color endpoint inequalities use exact rational arithmetic.

Replacing Fibonacci fusion by ordinary involutions X_a^2=I is not valid even after capping runs. The word abbacca wins by deleting bb, then cc, then aaa. Its three a's prevent an empty product in the proposed involution model. This failure is recorded explicitly in the checks.

## A second proof of decay for five colors, without analytic continuation

Group a word into blocks of three letters and a final block of length r<3. Within a triple, the only duplicate normal-form coefficient occurs for aaa: X_a^3=I+2X_a. Replacing this by I+X_a preserves its positive support on every input stack. Summing these modified operators over all b^3 triples gives the entrywise nonnegative operator B=T^3-T. Consequently the empty coefficient of B^k T^r is an integer upper bound on W_b(3k+r).

For the same h and lambda as above, write Th=lambda h-delta e, where e is the root indicator and delta=lambda-b/sqrt(b-1)>=0. Expanding exactly,

    Bh = (lambda^3-lambda)h
         - delta[(lambda^2-1)e + lambda T e + T^2 e]
       <= (lambda^3-lambda)h.

Both B and T have nonnegative entries; also e<=h and h(root)=1. Induction therefore gives

    W_b(3k+r) <= (lambda^3-lambda)^k lambda^r,  0<=r<3.

In particular,

    W_5(n)/5^n <= (24/25)^floor(n/3).

This elementary bound is weaker asymptotically than the run-normalized 129(40/41)^n bound, but proves the same five-color decay conclusion without Pringsheim's theorem or spectral theory. It still does not prove decay, or a scalar counting formula, for three or four colors.

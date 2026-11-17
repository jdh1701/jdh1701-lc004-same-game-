# Class-count bridge: precise next implementation

For p <= pi, no noncrossing hypothesis is needed for class-count additivity.
Define the forward map from Sigma q, Quotient (restrict p (embed pi q)) to
Quotient p by (q,[i]) |-> [embed pi q i]. Quotient.sound and restriction's
relation equivalence prove well-definedness. It is surjective by the regional
cover. For injectivity, p-equivalence implies pi-equivalence, hence equality of
q via patternRegionEmbed_class; after substitution, Quotient.exact plus the
restriction relation equivalence gives equality of local quotient classes.
Use Equiv.ofBijective on this map, Nat.card_congr, and Nat.card_sigma.

This construction works for arbitrary p <= pi, including n=0. Restricting it
to connectedClosureFiberEquiv then proves the exponent identity required for
weighted coefficient factorization. It does not need certificate enumeration,
a connectedness assumption, or an assumption about multiplicativity of weights.

Status: implementation plan; no claim of a newly checked Lean theorem here.

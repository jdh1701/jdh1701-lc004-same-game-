# Preserved failure map

Source 7fb686483e0cb4c6d8b9b1f37e897b2da1a8bba1, run41097517330:
exact job124206998443 passed; Lean job124206997870 failed.

The only build error is ConnectedFirstExcess.lean line90, the negative
class-count branch of connectedClassCoefficient_first_excess. Unrestricted
`simp [hk]` rewrites Nat.card to Fintype.card before applying the negative
hypothesis. The resulting conditional remains unresolved. The failed theorem's
printed dependency list includes sorryAx because Lean is reporting an unsolved
goal; this is NOT a verified theorem. No full axiom audit ran after the failed
build. The complete hosted log is retained.

The excess identity, the one-six-class support theorem, and both general
small-generator coefficient lemmas compiled in this run with standard axioms.
The fix is to restrict simplification to the negative hypothesis and conditional
rules, preserving its original Nat.card expression. A new full exact-source
build and audit are required before promotion.

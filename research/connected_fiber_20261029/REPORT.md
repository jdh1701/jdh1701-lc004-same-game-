# Connected closure fiber checkpoint

PROVED-LEAN (local Lean 4.19.0): closure equals a given noncrossing
coarsening iff every restriction to its blocks is NCConnected.
PROVED-LEAN: connectedClosureFiberEquiv is an explicit equivalence of the
closure fiber with the dependent product of local connected pattern spaces.
Both declarations use only propext, Classical.choice, Quot.sound.
Full root build passes. The theorem permits n=0.

VERIFIED-COMP: check_fibers.py checks all n=0..7 patterns, fiber cardinalities,
restriction injectivity, the connectedness criterion, and class-count
additivity. Class-count additivity remains to be formalized for arbitrary n.

Next: construct Quotient p equivalent to the sigma of regional quotients,
then derive additive class counts and multiplicativity of b^classCount.
Use the established coefficient product and fiber equivalence to obtain the
weighted closure pushforward and identify the moment-cumulant recurrence.
The effective enumeration of surviving connected weights remains unresolved.

Claude handoff: reuse this equivalence; focus complementary research on
connected-weight enumeration and decisive tests of the all-five conjecture.
No direct Claude invocation or new literature/Sage run occurred here.

attempt01 and attempt02 preserve elaboration failures; attempt03 is the
successful full build. Failed intermediate sources are not separately saved.

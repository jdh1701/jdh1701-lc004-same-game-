# Class-count and weighted component checkpoint

PROVED-LEAN (local Lean 4.19.0): regionalQuotientMap is bijective for every
p <= pi. regionalQuotientEquiv identifies global p classes with the disjoint
union of regional p classes. No noncrossing hypothesis is required.

PROVED-LEAN: pattern_class_count_regions gives additive class counts;
pattern_class_weight_regions factors b^classCount for every integer b.
PROVED-LEAN: weighted_winningJoinCoefficient_regions combines that identity
with the signed coefficient product for noncrossing coarsenings.
All statements include the empty pattern. Full root build passed; final
printed axioms are only propext, Classical.choice, Quot.sound.

This replaces the finite-only class-count evidence in the previous checkpoint
with an unrestricted formal proof. It does not yet identify free cumulants
or solve effective enumeration of the connected weights.

Next: sum weighted_winningJoinCoefficient_regions over connectedClosureFiberEquiv,
use Fintype.prod_sum, then regroup all patterns by closure. Integrate the
existing LabeledJoinEnumeration.lean from the primary repository to identify
the original game's labeled counts with this moment-cumulant formula.

Claude handoff: reuse this quotient equivalence and weight factorization;
focus complementary work on surviving connected-weight enumeration or
counterexamples to the all-five conjecture. No direct Claude call, new
literature search, or Sage computation occurred in this checkpoint.

attempt01.log preserves the failed elaboration; attempt02.log the successful
full build. Intermediate failed source versions were not separately retained.

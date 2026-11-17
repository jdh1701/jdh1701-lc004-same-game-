# Small-block cancellation through cyclic gaps

This is a proposed general proof in the partition-witness model, with its
formal boundary identified below. It is not an end-to-end Lean theorem for
the existing generator or raw game. No novelty claim has been established.

Later formal progress is recorded in [the four-gap checkpoint](../gaps/STATUS.md):
the regional witness intersection and positional regional cancellation are
now proved. The boundary below describes the earlier checkpoint; locality,
full-board/product transport, complete branch identification, and the final
minimum-five assembly remain open.

## Definitions and proposed conclusion

Let V_n be all noncrossing partitions of n cyclically ordered positions into
blocks of size two or three. Let a_n(p) be the collected signed coefficient
of p in the union of their equality events, taking joins in ALL partitions.
For a block B of p, list the cyclic gaps between successive positions of B
as G_1,...,G_m. An empty gap has coefficient a_0(empty)=1.

The proposed small-block formula, for m=2,3,4, is:

```text
a_n(p) = c_m * product_i a_|G_i|(p restricted to G_i)
         if every other block of p lies in a single cyclic gap;
       = 0 otherwise,
where c_2=1, c_3=1, c_4=-1.
```

In particular, if p is connected under crossing and has at least two blocks,
then nonzero a_n(p) requires every block to have at least five positions.
This does NOT say all size-four blocks vanish: a_4(0000)=-1.

## Locality before decomposition

Only witnesses refining p can contribute to a_n(p). Any join containing a
witness that does not refine p cannot equal p, since each input refines its
join. Thus witnesses connecting B to its complement may be discarded when
evaluating this particular coefficient. The remaining partitions form a
product: a partition on B and one on its complement. This locality and product
transport still require formal assembly in the Lean development.

Cyclic rotation preserves the noncrossing pair/triple witness family, joins,
and signed coefficients. Rotate so the first point of B is position zero.
The cyclic gaps then become ordinary ordered intervals, with the final gap
being the suffix. Formal rotation transport is also still outstanding.

## Blocks of size two or three

Every refining witness must contain B as one whole pair or triple. A different
noncrossing block cannot connect positions on opposite sides of a chord of B.
Thus all other witness blocks stay within one cyclic gap, and choices in the
gaps are independent. The coefficient is the product of the gap coefficients,
with coefficient +1 at the fixed B coordinate. Its support cannot connect
different gaps.

The general chord fact is proved in Lean as `noncrossing_interval_barrier`:
a block disjoint from two related endpoints cannot have one point strictly
between them and another outside. The partition-product assembly is not yet
formalized for this application.

## Four-position blocks: the two branches

Write B=(a,b,c,d) in order, and label the four gaps G_1,G_2,G_3,G_4. Every
refining witness uses one of exactly two noncrossing pairings on B:

- A: (a,b), (c,d).
- B: (a,d), (b,c).

The crossing pairing (a,c), (b,d) is forbidden. A singleton or four-position
primitive block is not an allowed pair/triple witness.

For a remaining equality partition r, let F(X) mean that its restriction to
the ordered subset X admits a pair/triple witness. The chord barriers give

```text
F_A(r) = F(G_1) F(G_3) F(G_2 followed by G_4),
F_B(r) = F(G_2) F(G_4) F(G_1 followed by G_3).
```

These values are 0 or 1. The formulas account for both inner intervals and
the region outside the two chords; they do not require different equality
classes to receive distinct colours. Concatenation of two valid gap witnesses
is a valid witness on their concatenation. Therefore

```text
F_A(r) F_B(r) = F(G_1) F(G_2) F(G_3) F(G_4).
```

The corresponding grammar conjunction identity is formally proved as
`four_gap_pairing_intersection`. Identification of the two displayed forced
pairing events with these gap conditions is tested exhaustively through n=10,
but still needs its general Lean construction and reconstruction proofs.

## Why the coefficient cancels

The join of the two B-coordinate pairings is the full four-position block,
proved as `quad_pairings_join_top`. Neither branch alone can produce this
full B-coordinate. Inclusion-exclusion at the coefficient level therefore
leaves minus the intersection coefficient. This exact statement is proved
for arbitrary finite semilattices by `two_branch_join_coefficient`.

Let g be the partition of the remaining positions into the four gaps. The
intersection indicator above depends only on r meet g: equality relations
between different gaps are irrelevant when all four gaps must separately
admit witnesses. Hence its cumulative coefficient function is invariant under
meet with g. `coefficient_zero_outside_barrier` proves that this invariance
forces all coefficients at r not refining g to vanish.

`four_block_barrier_zero` combines these algebraic statements for the actual
two setoids on Fin 4. Its explicit hypothesis `hinv` is the intersection
coverage invariance. This hypothesis has not yet been discharged in Lean for
the full Same Game witness family. The theorem does not assume coefficient
vanishing as a premise.

When r does refine g, the intersection family separates into its four gap
families. Product factorization gives the stated negative product formula.

## Connected support consequence

A singleton block cannot occur in a join of pair/triple witnesses. For a
block of size two, three, or four, the formula above requires that no other
block crosses it if its coefficient is nonzero. Such a block is then an
isolated component of the crossing graph. Therefore a connected partition
with at least two blocks and nonzero coefficient has all block sizes >=5.

If this argument and the component factorization are fully formalized, they
give `degree R_n(q) <= max(1,floor(n/5))`. The observed -5q^2 term at n=10 and
-35q^3 term at n=15 show the bound is attained at those finite lengths. They
do not prove attainment for all multiples of five or supply all connected
coefficients. A useful general recurrence is still needed.

## Exact formal boundary

Already compiled: cumulative-coefficient support under a meet barrier;
coefficient-level inclusion-exclusion; fixed-coordinate support; the two-branch
negative intersection identity; the four-position pairing join and conditional
cancellation theorem; the general noncrossing chord barrier; and the grammar
four-gap conjunction identity.

Not yet assembled: locality/filtering at a target partition; the partition
product order isomorphism and coefficient transport; rotation transport;
forced-pairing/gap witness equivalence and its explicit reconstruction;
and identification with the generator. The proposed general minimum-five
conclusion is therefore NOT counted as Lean verified.

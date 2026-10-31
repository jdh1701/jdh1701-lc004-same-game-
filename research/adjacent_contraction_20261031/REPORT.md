# Adjacent contraction closes the restricted cancellation gap

2026-10-31, America/New_York. Base: PR45, ff5d10c9041b5215c231182bc660f8a5da2cbc9b.

## Result and exact scope

**PROVED-PAPER.** Let p be a nontrivial NCConnected pattern, with a five-point
class containing two consecutive positions u,v. Other class sizes are arbitrary.
Let p+ insert another point of that class between u,v. Then

    kappa(p+) = kappa(p).

The previously open restricted term kappa_T(p) is zero. This follows from an
exact contraction correspondence with the ORIGINAL complete certificate family,
not from a finite census, an assumed two-generator classification, or a
survivor-only argument. The all-five case is an immediate special case.

The Lean source in this change targets the complete original restricted-family
coefficient identity and its vanishing, at the initial adjacent pair. Formal
status is recorded separately in receipts.json after hosted verification.
The inflation correction formula and its original-position gap assembly remain
paper proofs; this report does not label the whole inflation theorem Lean-verified.

The full LC004 counting problem remains OPEN. In particular, this does not
enumerate all-five survivors, exceptional first-excess survivors, or higher excess.

## The contraction lemma

Let q be p with u deleted, retaining v. Write pi for the order-preserving
surjection identifying the adjacent positions u,v, and sigma for the section
which retains v. The distinguished class of q has size four.

For a partition d on q, define D(d) by pulling its equivalence relation back
along pi. For a partition c on p identifying u,v, define C(c) by restricting
along sigma. The identities C(D(d))=d and D(C(c))=c hold exactly. Thus D is
injective and preserves refinement and every nonempty join: it is an order
isomorphism onto the equivalence relations identifying u,v. Empty joins are
deliberately excluded; D does not preserve the discrete partition.

Noncrossingness is preserved in both directions. A strictly alternating
quadruple in the expanded order either projects to four distinct ordered
points, or has coincident adjacent projections. In the former case apply
noncrossingness downstairs. In the latter case equivalence and transitivity
already identify the two alleged crossing classes. Conversely, a crossing
downstairs lifts along the increasing section sigma. This argument applies to
every coarsening, not only to certificates.

Consequently NCConnectedness is preserved in both directions. More explicitly,
any proper noncrossing coarsening downstairs pulls back to a proper noncrossing
coarsening upstairs. Any coarsening upstairs identifies u,v and therefore
contracts and lifts back exactly. The number of color classes is also unchanged.

Let F(q) be the complete original noncrossing 2/3 certificate family refining q,
and let

    T(p) = {c: c is an original certificate refining p,
               u and v lie in the same three-point block of c}.

A certificate refining a four-point color class must partition it into two
pairs. A triple would leave a singleton, which is forbidden. D therefore turns
the pair containing v into a triple containing u,v, with every other block
unchanged. It gives a map F(q) -> T(p).

Conversely, deleting u from a member of T(p) turns its designated triple into a
pair and leaves the other blocks unchanged. Refinement and noncrossingness are
preserved, so this is a member of F(q). These maps are inverse. They preserve
cardinalities of subsets and all nonempty joins. Hence the defining ORIGINAL
signed-join sums satisfy, without any connectedness assumption,

    kappa_T(p) = kappa(q).

If p is NCConnected and has at least two classes, so does q. The proved support
theorem `ncConnected_nonzero_every_class_min_five` says every class of a nonzero
such q must have at least five points. Its four-point class forces

    kappa_T(p) = kappa(q) = 0.

This is an unbounded proof and does not assume anything about the sizes of the
other classes. It uses the existing general four-class cancellation theorem
through the established connected-support theorem; there is no circular use of
inflation preservation.

## Finishing the inflation proof

PR45's [finite join-algebra proof](../inflation_law_20261031/TRANSFER_FORMULA.md)
establishes

    kappa(p+) = kappa(p) - 2*kappa_T(p) + gamma_U.

That proof was stated for all-five patterns, but its reduction treats the
complete outside certificate configurations as arbitrary partitions into pairs
and triples. Only the distinguished class uses a five-state catalogue. No step
uses a size-five restriction on another color class. The same proof therefore
applies with arbitrary other class sizes. The empty outside-family case simply
has every coefficient zero.

For a nontrivial connected pattern the distinguished class is crossed by
another color class. If every outside certificate block stays in one of its
gaps, their join still refines the gap partition, whereas that crossed outside
color class does not. Thus no nonempty subset of those outside configurations
joins to the outside pattern, and gamma_U=0. Combining this with the contraction
lemma proves kappa(p+)=kappa(p).

The two exclusions are essential. A single five-point class has kappa=-4;
after inflation the single six-point class has kappa=-1, and the contracted
four-point class has kappa=-1. Disconnected patterns can also have nonzero
restricted terms and universal corrections. The executable checks retain such
examples instead of dropping them.

## Consequences that now follow

1. In every nontrivial connected all-five complete two-generator full-join
   source, each adjacent equal pair is a pair-block in at least one generator.
   Otherwise the PR45 dichotomy would give inflated coefficient +1, contradicting
   preservation of the source coefficient -1. Equivalently T would contain both
   source generators and have coefficient -1, contradicting kappa_T=0.
2. The conditional +1/four-generator inflation branch is impossible for those
   connected sources. Its abstract four-generator coefficient calculation is
   still correct; the proposed actual-pattern realization is now excluded.
3. Inflating any such adjacent pair yields exactly three complete generators
   and coefficient -1. The earlier no-three-run theorem remains valid.
4. For a connected first-excess pattern with profile (6,5,...,5), at least two
   classes, and a three-run in its six-class, deleting one point of the run gives
   a connected all-five source with exactly the same coefficient. This identifies
   its nonzero triple-run layer with the inflation image of nonzero all-five
   sources. The three-generator conclusion applies when the contracted source
   has the established two-generator hypotheses; no unproved universal
   classification is substituted here.

The stronger assertion that every five-class in every survivor has cyclic run
multiset (1,2,2) is STILL OPEN. The current proof only gives runs of length at
most two for two-generator full-join sources and covers each existing two-run.
It does not prove that there are two such runs per class. Consequently an
all-length count using a constant 2j number of inflations remains conditional.

## Verification and reconciliation

`check.py` checks the actual certificate bijection, binary joins, connectedness,
restricted original signed sums, and inflated coefficients on its stated
exhaustive profiles and seeded probes. `checks.json` records exact counts.
It includes arbitrary other class sizes, disconnected inputs, singleton classes,
and the single-class exception. Smaller profiles and all seeded probes are also
replayed using the separate four-endpoint crossing test and original signed-join
dynamic program. The two paths share local catalogue generation, so independence
is partial. No random probes or repeated marked inputs are called a full census.

PR35 advanced from 352d5b54 to b0e3f9e4982edf374cc64574b2c8bd7867094903 with a
WORKBOARD review of PR44, and no new Lean modules. Claude independently confirms
the n11 result and the green n21 CI. His original wording was already
"22 nonzero connected patterns"; our earlier caution was a clarification, not
a correction of an error in his result. PR41-45 had no newer proof changes at
the reconciliation check.

No local Lean runtime is available. Only a green hosted full build and complete
axiom audit at the exact recorded source can promote a claim to PROVED-LEAN.

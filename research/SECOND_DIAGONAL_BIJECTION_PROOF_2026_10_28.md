# Second-diagonal count: explicit combinatorial derivation and formalization boundary

Date: 2026-10-28

## Statement and counting convention

Let A(n,k) count winning words of length n using exactly k colors, up to
bijective renaming of colors. Equivalently, count partitions of the ordered
position set into k nonempty color classes whose associated word wins.
Each such partition has exactly one restricted-growth labeling. These are
unlabeled color patterns, not the labeled words over an alphabet of size k.
The corresponding contribution to the count on q named colors is
A(n,k) times the falling factorial (q)_k.

The proposed second-diagonal formula has the simpler form

    A(2k+2,k) = k * binom(2k+2,k-1),       k >= 2.

The argument below uses the now Lean-verified structural characterization
and the classical refined enumeration theorem for noncrossing partitions.
It is a paper-level combinatorial derivation. The game-specific finite-set bijections and the Catalan matching count
are now formalized in Lean. The two refined noncrossing cardinalities
are NOT yet formalized.
This document must not be cited as a fully Lean-certified counting theorem.

## Inputs and their provenance

The structural theorem `LC004.raw_max_win_iff_certificate`, verified in
CI run 370 at source head 40f100a1982b1706e7d70a5945baf5a807e08ae9,
characterizes genuine maximal-run wins by complete monochromatic
noncrossing partitions into blocks of size two or three.

For ordinary noncrossing set partitions with m_j blocks of size j,
let B = sum_j m_j and n = sum_j j*m_j. The classical Kreweras number is

    n! / ((n+1-B)! * product_j m_j!).

Reference: Jang Soo Kim, *Chain enumeration of k-divisible noncrossing
partitions of classical types*, arXiv:0908.2641, equation (5), which
attributes the result to Kreweras, Theorem 4. Equation (5) is stated as
(1/B) * multinomial(B; m_1,...,m_n) * binom(n,B-1), which is exactly
the factorial expression above.
https://arxiv.org/pdf/0908.2641

Here ordinary noncrossing means that DISTINCT color classes do not cross.
A coarse block of size four is NOT tested against itself. This differs
from the repository's stronger `NoncrossingBlockFamily` predicate, whose
self-comparison is harmless only for blocks of at most three positions.
The four-point coarse partition below uses the ordinary convention.

## 1. Exhaustive multiplicity profiles

Every used color in a winning word occurs at least twice: a color
occurring once cannot participate in any monochromatic deletion.
If n=2k+2 and there are exactly k used colors, the sum of the excesses
over multiplicity two is exactly two. Hence the only possibilities are

* one color class of size four and k-1 classes of size two;
* two color classes of size three and k-2 classes of size two.

These profiles are disjoint. The counting-specific Lean module
`SecondDiagonalProfiles.lean` states and proves the corresponding
universal reduction; its current CI status must be checked separately.

## 2. Fourfold profile: define the representation map

Put n=2k+2. A representation is a noncrossing perfect matching M on
the n ordered positions together with an unordered choice of two edges
of M. Merge those two edge blocks into one color class of size four;
leave every other edge as its own color class. The resulting partition
has the fourfold profile and is winning, since M is a valid pair-only
monochromatic certificate for its word.

Conversely, a winning partition of this profile has a pair/triple
certificate. A two-occurrence color must form one pair. The fourfold
color must form two pairs: three plus a leftover singleton is impossible,
and singleton blocks are prohibited. Therefore the certificate is a
noncrossing perfect matching and the fourfold color identifies the
unordered chosen pair of its edges. The representation map is onto the
winning fourfold-profile partitions.

There are Catalan(k+1) matchings and binom(k+1,2) choices of two edges,
so the representation count is

    R = binom(k+1,2) * Catalan(k+1).

## 3. The fibers have size one or two, with an exact overlap condition

Fix a fourfold-profile partition and write its four repeated positions
as a<b<c<d. All other pair edges are forced. A perfect matching on the
four selected positions has exactly one of the three internal pairings

    (a,b)(c,d),     (a,d)(b,c),     (a,c)(b,d).

The last pairing crosses internally and cannot occur in a noncrossing
representation. Thus a winning partition has either one or two
representations. For a fixed matching and resulting partition the chosen
two edges are determined by the unique fourfold color, so this argument
does not hide another representation multiplicity.

Both remaining internal pairings are compatible with all forced edges
if and only if the original coarse color partition is noncrossing.
To see this, forced edges must first be mutually noncrossing. For one
forced edge u<v, disjoint from a,b,c,d, compatibility with both choices
means absence of crossing with each of (a,b), (c,d), (a,d), and (b,c).
The verified local four-point criterion identifies this precisely with
not crossing the coarse four-point block. Requiring it for every forced
edge gives the ordinary noncrossing condition for the coarse partition.

Therefore the doubly represented objects are in bijection with ordinary
noncrossing partitions of type m_4=1, m_2=k-1. The Kreweras formula gives

    D = (2k+2)! / ((k+3)! * (k-1)!) = binom(2k+2,k-1).

If W_4 is the number of winning fourfold-profile partitions, then
R = W_4 + D: each object is counted once, plus one extra count exactly
when it has two representations. Consequently W_4=R-D.

`FourRefinementOverlap.lean` formalizes the arbitrary-forced-family
geometric overlap and the cardinality of valid internal refinement
choices. `DoubleRepresentationCount.lean` formalizes the finite
one-or-two-fiber counting identity with explicit surjectivity and fiber
bound hypotheses. Neither module by itself constructs the entire
global representation-to-pattern bijection used in this section.

## 4. Two triples: a direct bijection

Every two-occurrence color must be one pair in a certificate. Every
three-occurrence color must be one triple, since a pair would leave a
singleton. Thus a winning pattern of the second profile is itself an
ordinary noncrossing partition of type m_3=2, m_2=k-2.
Conversely, each partition of that type is a valid complete certificate
and therefore wins under the structural equivalence. This is a
bijection, not a count of deletion histories.

The classical refined count is

    T = (2k+2)! / (2! * (k-2)! * (k+3)!).

## 5. Add the disjoint profiles and simplify

The complete paper-level enumeration is A(2k+2,k)=R-D+T. In terms of D,

    2R = (k+3)D,     2T = (k-1)D.

These follow by canceling factorials in the Catalan and binomial
expressions. Hence

    2A = (k+3)D - 2D + (k-1)D = 2kD,

which gives A(2k+2,k)=k*binom(2k+2,k-1).
For k=2,...,7 this yields 12, 84, 480, 2475, 12012, 56056, agreeing
with the earlier independent checks. Finite checks do not prove the
universal counting formula.

## Current formalization boundary (updated 2026-10-28)

The actual finite color-pattern spaces, exhaustive and disjoint intrinsic
profile split, representation surjection, one-or-two fiber count, and
both conventional noncrossing correspondences are now Lean theorems.
`MatchingCatalan.lean` also proves the exact noncrossing matching count
through a full bijection with Dyck words. These passed CI at head
3c2f9ad8593d3269d66e2432030f325944e96d43.

`SecondDiagonalArithmetic.lean` proves the coefficient identity
2R=(k+3)*binom(2k+2,k-1), handles natural-number subtraction, and
assembles the final formula CONDITIONAL on the two refined counts.
This initial arithmetic assembly passed CI at head
3746a5a6cbd02a74ff45b91eb267362beeefe363. Subsequent parity and encoding
extensions must be checked at their own source heads.

Exactly two universal cardinality evaluations remain:

* N4(2k+2) = binom(2k+2,k-1).
* 2*N33(2k+2) = (k-1)*binom(2k+2,k-1).

No unconditional closed counting formula is claimed. General n,k
enumeration and any novelty claim remain outside what has been proved.
The earlier descriptions in sections 2--4 that a local module alone
does not supply a global bijection remain true of those individual
modules; the later modules now supply those bridges.

## Next counting route: rooted-tree degree words

Record a block's size at its least position, put zero at all other
positions, and append one terminal zero. The resulting list has length
n+1, total degree n, and every proper prefix has degree sum at least its
length. `PartitionOpeningMass.lean` develops these invariants and the
correspondence between positive arities and original block sizes.
Its source must be compiler-checked before being called a proved bridge.

The missing universal steps are injective reconstruction for conventional
noncrossing partitions, surjectivity onto the valid degree words, and the
rotation counting argument. In a list of length n+1 with total degree n,
exactly one rotation is valid and each orbit has size n+1. For fixed block
multiplicities m_j, the degree multiset has m_j copies of j and
n+1-sum(m_j) zeros. Counting the multiset words and dividing by the orbit
size gives the refined factorial formula used above. These universal
bijection and rotation assertions are the intended proof obligations,
not imported axioms or established Lean results.

`check_partition_degree_encoding.py` independently enumerates fixed-profile
set partitions and degree words for lengths 6, 8, and 10. It checks exact
image equality, injectivity, full rotation orbits, unique valid roots,
and the expected finite cardinalities. Passing finite tests does not prove
the universal assertions.

The executable inverse uses a stack of pending block slots. A positive
degree opens a new block at that position and pushes size-1 pending slots;
a zero fills a slot in the most recently opened unfinished block. The
terminal zero is omitted. Prefix balance ensures that a zero never faces
an empty stack, and total balance ensures that all blocks close. The
finite checker verifies that this decoder returns the exact original
partition for every tested valid word. Formal invariants for this stack,
its noncrossing output, and the two inverse laws remain to be proved.

A specialized counting route can avoid a general multinomial theorem.
For the fourfold profile, rotate the unique degree-4 entry to the first
position. The remaining degree-2 positions form a (k-1)-subset of the n
remaining positions, yielding binom(n,k-1). For the two-triple profile,
mark one of the two degree-3 entries and rotate it first. Choose the other
degree-3 position in n ways and the k-2 degree-2 positions from the other
n-1 positions. The resulting marked count is
n*binom(n-1,k-2)=(k-1)*binom(n,k-1), and marking multiplies the unmarked
count by two. Both routes still require the universal decoder inverse
and unique valid rotation theorem; the elementary choice counts alone
do not evaluate the partition spaces.

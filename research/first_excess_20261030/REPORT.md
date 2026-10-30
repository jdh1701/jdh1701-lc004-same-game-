# First excess: a uniform profile theorem and the complete (5,5,6) census

2026-10-30. The general enumeration problem remains open. This continuation
identifies the only possible profile one position above the connected support
threshold and independently exhausts its first three-class case.

## Repository reconciliation and proof status

Base: PR42 receipt `b04947b4de92115b7caf8e17f5a0195e5efc15be`. Its exact proof
source `f653c28b15697dd6b9a4b53771fe46beeeb83986` is green in run41029475200.
PR35 has advanced to `2f62dfe02dda3073ef0f238da847020dd91d8ac5`, adding finite
crossing-lemma checks and a proof sketch. Those do not supersede PR42's general
Lean proof of the lemma, its support theorem, or its interpolation theorem.

The earlier checkout and Lean runtime were not available in this execution
environment. A fresh checkout was restored. The new Lean source is sent to
hosted compilation; it is not represented as locally compiled. The local
negative-axiom test failed to start because `lake` was absent, and that log is
retained. See receipts.json for the final exact-source hosted status.

## General first-excess theorem

For an NCConnected pattern p with j>=2 classes and nonzero original coefficient,
the already-proved support theorem gives class sizes s_q>=5. The new theorem
records the exact identity

    sum_q (s_q - 5) = n - 5j.

At n=5j+1, these nonnegative integer excesses sum to one. Some excess is nonzero;
each is at most the total one, so that excess is one. Removing its summand leaves
sum zero, forcing every other excess to zero. Therefore there is exactly one
six-point class and every other class has size five.

`ConnectedFirstExcess.lean` formalizes this argument and restricts the ACTUAL
`connectedClassCoefficient (5*j+1) j` sum to this profile. It does not assign
values to the surviving coefficients or assume their signs.

`SmallGeneratorCoefficients.lean` gives two general original-coefficient rules:

- A complete family of two proper certificates whose join is p contributes -1.
- A complete family of three proper certificates with exactly two top-joining
  pairs contributes -1: the two pairs contribute -2 and the triple contributes +1.

These are universal conditional lemmas about the original coefficient. The
individual finite pattern families below are computationally replayed, not
silently treated as Lean-certified instances.

## Exhaustive finite result

The first census enumerates every partition of sixteen original positions into
two unordered five-classes and one six-class:

    choose(16,6) * choose(10,5) / 2 = 1,009,008.

| Quantity | Count |
|---|---:|
| All (5,5,6) patterns | 1,009,008 |
| NCConnected patterns | 999,736 |
| Connected patterns with at least one certificate | 109,720 |
| Connected patterns with full certificate join | 3,384 |
| Nonzero connected coefficients | 312 |
| Zero connected coefficients | 999,424 |
| Sum of connected coefficients | -312 |

Every nonzero value is -1. There are 88 complete two-certificate families and
224 complete three-certificate families. In every two-certificate case the pair
joins to p. In every three-certificate case exactly two pairs join to p. Thus
the two new general coefficient rules explain all surviving signs in this census.

The signed-join dynamic program uses 16 six-class join states, together with
the two five-class join states. It skips coefficient evaluation only when the
join of ALL original generators is proper, which forces zero by the existing
common-refinement theorem. Every intermediate integer is checked below 2^50;
the next addition/subtraction cannot overflow signed 64-bit arithmetic. The
assertions remain enabled in the build. Connectivity is computed by crossing
merges on original class masks, not assumed from the profile.

## Independent census

`independent.py` does not use the C++ compatibility or join tables. It generates
all relevant noncrossing 2/3 certificates on the original sixteen positions:

- 24,024 with five pairs and two triples;
- 10,920 with two pairs and four triples.

Grouping these original blocks into the (5,5,6) profile yields 611,520
certificate-pattern incidences and 115,536 distinct patterns with certificates.
Connectivity is checked by exhausting the proper coarsenings of three classes.
Separator faces are built directly from the original certificate blocks, then
evaluated by their exact alternating sum. This reproduces the entire 312-pattern
nonzero set, its coefficients, and all 3,384 full-join cases.

Every nonzero case is checked again by direct signed joins over all subsets of
its two or three original certificates, as are 500 zero cases with at most eight
certificates. `classify.py` separately regenerates the complete local family and
checks its top-joining pairs for every survivor. Patterns without any original
certificate have coefficient zero by definition, not by an empirical guess.

The total -312 agrees with the cubic connected coefficient at n16 inferred in
the preceding campaign from known ternary counts. The new result is a direct
structural enumeration of that coefficient, not a new ternary sequence term.

## The simplest inflation strategy fails

For each survivor, delete each of the six positions in its six-class in turn.
Test whether the resulting (5,5,5) pattern is connected and has coefficient -1.

| Surviving family | Patterns | Successful deletions per pattern |
|---|---:|---:|
| Three certificates | 224 | 3 |
| Two certificates | 88 | 0 |

All three successful deletions in the first row are adjacent, in the cyclic
order, to another position of the six-class. The 88 cases in the second row
refute the claim that every first-excess survivor comes from inflating an
all-five survivor, even when arbitrary single-position insertion is permitted.

The six-class restrictions of the original certificates have three types:

| Restrictions on the six-class | Patterns |
|---|---:|
| Three pairs, three pairs, two triples | 224 |
| Three pairs, two triples | 80 |
| Three pairs, three pairs | 8 |

There are 22 cyclic orbits (17 of size16 and 5 of size8) and 12 dihedral orbits
(8 of size32, 3 of size16, and 1 of size8). Full representatives, their original
certificates, and pair-join graphs are in classification.json. No implication
for arbitrary j is inferred from this finite classification.

## Reproduction and next obligation

```sh
python research/first_excess_20261030/prepare.py
g++ -O3 -std=c++17 -Wall -Wextra -Werror research/first_excess_20261030/count.cpp -o /tmp/count556
/tmp/count556 research/first_excess_20261030/tables.txt research/first_excess_20261030/nonzero.txt > research/first_excess_20261030/count.json
python research/first_excess_20261030/independent.py
python research/first_excess_20261030/reductions.py
python research/first_excess_20261030/classify.py
lake build LC004
lake env lean scripts/AxiomAudit.lean
python scripts/check_lean_coverage.py
python scripts/test_verification_guards.py
```

The next structural obligation is to explain the two-certificate first-excess
families for arbitrary j, and determine whether the observed two/three-generator
classification survives beyond j=3. It is a question, not a theorem. Counting
the all-five survivors for arbitrary j and every higher-excess layer also remains
open; the (5,5,6) census does not solve the all-length problem.

## A countable inflation family

There is a more precise surviving part of the inflation idea. In all certified
all-five survivors at n10, n15, and the saved exhaustive n25 orbit fixtures,
each class occupies two cyclic runs of length2 and one run of length1. Inflate
one length2 run to length3. Complete original-certificate regeneration verifies
that every tested inflation has exactly three generators and coefficient -1.
The n25 check covers ALL 767 marked orbit fixtures and 7,670 distinct
representative inflations, not just the initial 200-case probe.

| j | All-five parents S_j | Distinct inflated patterns at length 5j+1 |
|---|---:|---:|
| 2 | 5 | 22 |
| 3 | 35 | 224 |
| 5 | 6,455 | 67,132 |

The n16 image is exactly the three-generator part of the exhaustive census.
At n26 this is a verified family of 67,132 distinct connected contributions,
each -1; it is NOT an exhaustive n26 first-excess census. The rest of the
n26 contributions, and the total connected coefficient, remain unknown here.

**PROVED-PAPER, conditional counting identity.** Let A be any rotation-invariant
set of partitions of 5j cyclically ordered positions, j>=2, with each class
having cyclic run lengths1,2,2. Let I(A) be its image under inflating one
length2 run. Then

    |I(A)| = 2(5j+1)|A|/5.

Proof: each source has 2j eligible runs. Rotation acts freely on source/run
pairs because fixing the marked run fixes its starting boundary. Hence there
are |A|*2j/(5j) marked-source orbits. Every image has exactly one length3 run,
so rotation acts freely on images as well. Contracting that unique run gives
a well-defined inverse on marked-source orbits, independent of which of its
three equal positions is deleted. Therefore each marked-source orbit gives
one image orbit of size5j+1, proving the formula. This counts inflation images;
it does not assert that their game coefficients are nonzero.

For the stated finite game families, the run hypothesis and coefficient
preservation are independently checked by complete local certificate families.
All rotated/reflected patterns are counted as explicit normalized words.
Transport preserves coefficients: a dihedral permutation preserves cyclic
alternation, certificate block sizes, and partition joins, hence bijects every
signed certificate subfamily. `inflation.py` reproduces these checks and counts.
Uniform run structure and coefficient preservation for arbitrary j remain
CONJECTURES, and even proving them would leave the 88 irreducible n16 cases
and their higher-j analogues to enumerate.

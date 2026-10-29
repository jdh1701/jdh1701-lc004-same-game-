# All-five cancellation by elimination of implicational constraints

Status: **PROVED-PAPER**, subject to independent review of this written proof.
This is not a claim that the full fixed-q enumeration problem is solved.
Four supporting lemmas compile locally in `LC004/ChoiceComplexCancellation.lean`;
the complete theorem below is not formalized in Lean. See `REPORT.md` for CI receipts.

## 1. The statement

Let p be a partition into j classes of size five, with j >= 2, whose least
noncrossing coarsening is the one-block partition. Let A be its set of
noncrossing pair/triple certificate refinements. Then

* if A consists of exactly two certificates and their join is p, c(p) = -1;
* in every other case, c(p) = 0.

In particular, three or more certificates always cancel. The argument counts
no patterns and provides no formula for the number of surviving pairs.

## 2. Local choices and the alternating face sum

In each five-class a certificate consists of one pair and its complementary
triple. The pair must be adjacent in the cyclic order on that class. There
are five choices. Number the positions 0,1,2,3,4 in increasing order and number
the pairs `(0,1), (0,4), (1,2), (2,3), (3,4)` by 0,1,2,3,4 respectively.
Thus A is a subset of a product of j five-element sets. It is defined entirely
by binary constraints: the chosen two blocks of each class must not cross
either chosen block of any other class. This condition is exactly global
noncrossing, since crossing is a pairwise obstruction.

Two distinct two-block partitions of the same set have join equal to the
one-block partition. Consequently a nonempty subset S of A joins to p exactly
when no coordinate is constant on S. Inclusion-exclusion on the constant
coordinates, followed by the identity
sum over nonempty subsets of a nonempty fiber of (-1)^(|S|+1) = 1, gives

    c(p) = sum over T subset [j] of (-1)^|T| * |projection_T(A)|.

Here c is the collected join coefficient: inclusion-exclusion of certificate
events has the original winning indicator as its lower-incidence sum, so
incidence inversion identifies its coefficients with c. No ordering or
duplication of a certificate list is relevant to this characterization.

Form the finite simplicial complex K(A) whose facets are the sets
`{(i,a_i): i in [j]}` for a in A. Its faces with coordinate set T are precisely
the members of projection_T(A). The displayed quantity is therefore
the alternating sum of all faces, including the empty face, or minus the
reduced Euler characteristic when A is nonempty.

If a coordinate is constant, K(A) is a cone and this sum is zero. If A is
empty it is zero as well. If A consists of two vectors differing at every
coordinate, its facets are disjoint simplices, so the sum is -1. If the two
vectors agree somewhere, the constant-coordinate argument applies.

It remains to treat |A| >= 3 with no constant coordinate.

## 3. Complete local compatibility classification

Use 0 and 1 for the two five-classes. Rotation, reflection and exchange of
the two class names preserve compatibility, up to renaming local choices.
The following table lists every orbit of the 126 words with five zeroes and
five ones and first symbol zero. The size column counts members of that
126-element set. It sums to 126. The representatives are inequivalent under
the stated operations; their orbit sizes can be checked by applying those
operations directly. Hence this is exhaustive. The entries in E follow by
testing alternation of each pair of the four proposed blocks, using the
explicit five local pairs listed above.

| Representative | Size | Compatible pairs E |
|---|---:|---|
| 0000011111 | 5 | all 25 pairs |
| 0000101111 | 10 | empty |
| 0000110111 | 20 | `(a,0)` for every a |
| 0001010111 | 10 | empty |
| 0001011011 | 20 | `(4,2)` |
| 0001011101 | 5 | `(4,1)` |
| 0001100111 | 10 | `(a,0)` for every a, and `(4,b)` for every b |
| 0001101011 | 10 | empty |
| 0010011011 | 5 | `(0,2), (3,4)` |
| 0010101011 | 10 | empty |
| 0010101101 | 10 | empty |
| 0010110011 | 10 | `(0,2)` |
| 0101010101 | 1 | empty |

Thus the possibilities are universal (the noncrossing case), empty, a relation
forcing one coordinate, a two-fan `x=s or y=t`, and a matching of size two.
The exact 126-case computation in `structure.py` independently checks this
table. `pair_orbits.py` checks all listed orbit representatives and sizes.

In the case still under consideration, empty and coordinate-forcing relations
are impossible. So every nonuniversal constraint is a two-fan or a matching
of size two.

The graph of crossing original classes is connected. To see the equivalence
with the stated noncrossing-closure hypothesis, fix an outside class C.
Every class not crossing C lies in one cyclic gap of C. Two such classes
in different gaps cannot cross each other. Hence each connected component
of the crossing graph lies in a single gap of every outside class. Taking
unions within a component creates no crossing with any outside class.
Applying the same argument after such a union shows that unions of distinct
components do not cross. The resulting component partition is noncrossing,
and every noncrossing coarsening must merge endpoints of each crossing edge.
It is therefore exactly the least noncrossing coarsening.

## 4. An abstract constraint theorem

Consider a finite binary constraint system on at least two variables. Suppose
its nonuniversal-constraint graph is connected, and its nonuniversal relations
are two-fans or matchings of size at most two. Let A be its solutions. If
|A| >= 3 and no coordinate is constant, K(A) strongly collapses to a point.

Domains below always mean the values occurring in actual solutions; they are
nonempty and have size at least two. Restricting a two-fan to these domains
leaves both pivots: omitting one pivot would force the opposite coordinate
to be constant. It therefore remains a proper two-fan. A matching constraint
restricts to a bijection between two-element domains.

### 4.1 Exact pair projections are 0/1/All relations

On any domain define m(x,y,z) to be y if y=z, and x otherwise. This conservative
majority operation commutes with bijections. Universal and matching relations
are closed under coordinatewise m. Two-fans are also closed: for three pairs
satisfying `x=s or y=t`, if the output x is not s, either the second and third
x values agree outside s, forcing both corresponding y values to t; or the
output x is the first x, forcing its y to t. In the latter case an output
y different from t would require the second and third y values to agree
outside t, forcing their x values to agree at s, a contradiction.

Thus A and every projection of A are closed under m. If an exact pair
projection contains (x,y), (x,z) with y != z and contains (u,w), applying m
to `(u,w), (x,y), (x,z)` produces (x,w). Every row having at least two entries
therefore contains the entire opposite supported domain. The same holds for
columns. Each row and column has either one or all entries.

A full-support relation on domains of size at least two with this property is
universal, a bijection, or a two-fan. Here is the elementary classification.
If every row has one entry, no column can be full (it would consume all rows
and leave another supported column empty); all columns have one entry, giving
a bijection. Otherwise there is a full row. Unless the relation is universal
there is exactly one full row: two full rows would force every column full.
Each other row has one entry; its column, having an entry from the full row
as well, must be full. There is exactly one such full column, since two would
force every row full. This is precisely a two-fan.

### 4.2 Eliminate bijective coordinates

Put variables in the same class when one determines the other bijectively
on A. This is an equivalence relation (compose the bijections). Retain one
representative of each class. Every removed vertex (i,x) is dominated in K(A)
by the retained vertex (r,f(x)): every facet containing the former contains
the latter. Delete the removed vertices one at a time. These are strong
collapses, and the remaining complex is exactly K(B), where B is the projected
solution set on representatives. The projection is bijective on solutions.

Substitute these bijections into the original constraints. This expresses B
again as a binary constraint system. Constraints inside a merged class are
satisfied by every supported value, by the definition of supported domain.
Constraints across classes are proper two-fans: a matching would identify
the classes, and a two-fan stays proper under bijective relabeling and the
supported-domain restriction just established. Therefore if at least two
representatives remain, their nonuniversal constraint graph is connected.
Its exact pair projections are also nonuniversal on these edges.

Only one representative cannot remain when |A| >= 3. In that case all
variables are bijective copies of one another with |A| supported values.
There was an original nonuniversal edge. A matching edge allows at most two
such values. A two-fan also contains at most two pairs from any bijection:
only one pair can use its row pivot and only one can use its column pivot.
Thus |A| <= 2, a contradiction.

### 4.3 A sink value supplies a cone

On the remaining supported vertices put an arrow `(i,x) -> (k,y)` for i != k
when every solution containing (i,x) contains (k,y). A directed cycle would
give mutual implication between vertices of two different variables. The
corresponding exact pair projection would have a row and column both singleton
at their intersection. Among the three types in 4.1 only a bijection can do
this. Such variables would already have been merged. The graph is acyclic.

A finite acyclic graph has a sink (i,x). Its row in every exact pair projection
is full, since a singleton row would give an outgoing arrow. Consequently
replacing coordinate i in any solution of B by x gives another solution:
all binary constraints touching i remain satisfied and all others are unchanged.
This uses the binary description of B, not an unjustified extension property
for arbitrary relations.

Connectedness gives a nonuniversal edge from i to some k. Its exact projection
is a two-fan with row pivot x and column pivot y. Every other vertex (i,u)
is therefore dominated by (k,y). Delete all these vertices. Any facet that
loses its i-value is contained in the facet obtained by replacing that value
by x. Thus the resulting complex is a cone with vertex (i,x). Delete its
other vertices, each dominated by (i,x), to leave a point.

This proves the abstract theorem and, by Sections 2 and 3, the all-five
cancellation theorem in Section 1.

## 5. The exact invariant used by a strong collapse

For completeness, deleting a dominated vertex v with dominator w preserves
the alternating face sum. Among faces containing v, pair a face with the
face obtained by toggling w. Both are faces: downward closure permits removal,
and the facet domination condition permits insertion. The two faces have
opposite signs and this is a fixed-point-free involution. All other faces
remain. This proof is formalized in Lean as
`faceAlternatingSum_delete_dominated` and
`facetAlternatingSum_erase_dominated`.

The majority preservation and row-completion steps of Section 4.1 are also
formalized as `twoFan_closed_choiceMajority` and
`choiceMajority_closed_row_all`. The classification, functional reduction,
acyclicity, game-to-complex identification, and final assembly remain to be
formalized. Local compilation is not a substitute for those missing bridges.

## 6. Literature and scope

Zhang, Yap and Jaffar, *Functional Elimination and 0/1/All Constraints*,
AAAI 1999, https://cdn.aaai.org/AAAI/1999/AAAI99-026.pdf, studies this exact
constraint family and functional elimination. It supplied the useful framework.
Its algorithmic satisfiability results alone do not establish the alternating
sum theorem above; that argument has been written out here. No priority or
novelty claim is made.

The finite checks are additional error detection, not the universal proof:
the construction in Section 4 has been executed and independently replayed
on all 38 nonfrozen geometric examples from our earlier sample and on all
2,640 distinct nontrivial relations in the four-binary-variable stress test.
Mixed-size classes do not have this local classification; the earlier
mixed-size counterexamples still stand. The number of surviving certificate
pairs and the general connected kernel remain open.

The abstract hypotheses cannot be dropped. Two independent binary coordinates
have four solutions and alternating sum 1 (the complex is a four-cycle);
their constraint graph is disconnected. A bijection on three values has
three solutions and alternating sum -2 (three disjoint edges); it violates
the matching-size restriction. Thus majority closure by itself does not
establish the theorem.

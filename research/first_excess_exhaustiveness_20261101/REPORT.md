# Uniform first-excess exhaustiveness

Base: 5c1e23172e492b8dd6c5aaf33ea4a0fb2beee61c (PR48 receipt).
Date: 2026-11-01 UTC. The full LC004/A035617 problem remains OPEN.

## Result and verification boundary

**PROVED-PAPER, with exhaustive finite computer checks as inputs:** Let p be
nontrivial NCConnected, with j >= 2 classes of sizes (6,5,...,5), and let its
ORIGINAL signed-join coefficient kappa(p) be nonzero. Then:

1. Its complete original certificate family has exactly two or three members.
2. Its coefficient is -1. Every five-class has cyclic run lengths (1,2,2).
3. The three-member case has a three-run in the six-class. By the earlier
   inflation theorem it has exactly one three-run, no longer run, and is the
   inflation of an all-five survivor. The two-member case has no three-run.

There is no bound on j in this argument. In particular it discharges the
first-excess obligation stated in PR48's HANDOFF.md. Combined with the two
complete stratum enumerations, the first-excess totals at j=2,3,4,5 are
22,312,5607,116857. The last value is no longer merely a lower bound **at the
paper-proof verification level**. These are not A035617 terms.

The proof below uses the previously certified covered-binary cancellation,
original face formula, and crossed-small-class vanishing. It also uses the
previous paper assembly of cyclic contraction, common-gap adjacency, and
five-class no-three-run. New local statements in SixBoundaryLists.lean target
the arbitrary-index Helly argument, the six-cut incidence and two-fibre facts,
and the four-gap star switch. Hosted verification status is recorded separately
in receipts.json. The complete original-position assembly in this report is
NOT a Lean theorem. In particular, the new 462-interleaving geometry and its
23,716 composed relations are exhaustive Python checks, not Lean-certified
geometry transport. Do not describe the full result as kernel checked.

## 1. Notation and exact finite boundary geometry

Number the six-class H cyclically by 0,...,5. Use the Lean catalogue order:

| State | Blocks |
|---|---|
| 0 | 012 / 345 |
| 1 | 015 / 234 |
| 2 | 01 / 23 / 45 |
| 3 | 01 / 25 / 34 |
| 4 | 03 / 12 / 45 |
| 5 | 045 / 123 |
| 6 | 05 / 12 / 34 |
| 7 | 05 / 14 / 23 |

For a five-class i and its local pair/triple state x, let N_i(x) be the set
of six-states compatible with its actual-position blocks. The exact finite
list family L consists of the empty set, the eight singletons, all eight states,
and these six pairs:

    {2,3}, {2,4}, {2,7}, {3,6}, {4,6}, {6,7}.

These pairs are the edges of K_{2,3} with parts {2,6} and {3,4,7}. States
0,1,5 are isolated. Every row N_i(x) belongs to L. This is checked directly
on all C(11,5)=462 five/six interleavings; there are 154 distinct row matrices.
The check uses original 2/3 blocks, with no presumed support or run shape.

The following additional facts are checked over those SAME actual matrices:

* If two full classes cross, their matrix has at most one all-eight row.
  If they do not cross, all five rows are all-eight.
* Every set of at least three nonempty rows in one matrix has a common state.
* For any two matrices R,S, the composed relation
  E(x,y) iff R(x) intersects S(y) is, on its supported domains, universal,
  empty, a two-fan, or a two-element bijection. The respective counts over
  all 154 squared ordered pairs are 14135,8105,1328,148. No larger bijection
  occurs. Two-fan means x=a OR y=b, on the supported rectangle.

The last classification gives conservative-majority closure and a one-row /
one-column cover for every nonuniversal relation on nonconstant supported
domains. Restrictions preserve closure; a nonuniversal supported restriction
cannot arise from an originally universal rectangle. The already established
five/five geometry has the same closure and cover properties.

L is intersection closed and 2-Helly: a pairwise-intersecting family has a
common element. To prove this for an arbitrary number of lists, choose a
proper member of size <=2; if all lists are universal there is nothing to do.
A singleton forces its element into every list. For a pair {x,y}, if neither
is common, choose lists omitting x and y respectively. Together with {x,y}
these would be three pairwise-intersecting lists with empty total intersection.
That cannot occur: the only two-element members are edges of a triangle-free
graph. Empty members are excluded by pairwise intersection, including a list
with itself. SixBoundaryLists.lean gives the arbitrary-index version.

## 2. Eliminating H is exact, for any number of five-classes

Let A0 be the complete noncrossing assignment family on the five-classes alone.
For a in A0 put D(a)=intersection_i N_i(a_i), and let

    A = {a in A0 : D(a) is nonempty}.

This is exactly the projection of the complete original certificate family,
with H forgotten. By 2-Helly it is specified by the original five/five binary
constraints, the unary conditions N_i(a_i) nonempty, and the binary constraints
N_i(a_i) intersects N_k(a_k). No consistency or extension assumption is hidden
in this specification. It is majority closed. After restricting each coordinate
to the values that actually occur in A, it is an ordinary binary constraint
system of the kind required by the existing cancellation theorem.

For any assignment family X write K(X) for its choice complex, with one vertex
(i,x) for each selected local state. Set beta(K)=sum_faces (-1)^card, including
the empty face. An absent family gives the empty complex and beta=0. Let

    P=K(A),  B=beta(K(A0)),
    K_t=K({a in A0 : t in D(a)}).

IMPORTANT: K_s intersection K_t is an intersection of FACE complexes. It need
not equal the choice complex of the common complete assignments. The proof
never makes that erroneous replacement.

## 3. The Euler correction terms are original coefficients

Let S_t be the set of six-cuts above local state t. Its size is one for a
triple state and three for a matching. Distinct S_s,S_t intersect exactly on
the six K_{2,3} edges, in one cut each; no three distinct facets intersect.
The original indexed face formula represents kappa(p) by the complex

    union_t (K_t * simplex(S_t)).

The intersection over a set T of these joins equals the intersection of the
K_t, joined to the simplex on the intersection of S_t. A nonempty common
six-cut makes that intersection a cone, with beta=0. Inclusion-exclusion,
compared with P=union_t K_t, therefore gives the exact formula

    kappa(p) = beta(P) - sum_t beta(K_t)
                         + sum_{edge {s,t}} beta(K_s intersection K_t).       (1)

For an edge e={s,t}, let E_e be the ordinary choice complex with one extra
binary coordinate, using value s over K_s and t over K_t. Its two pieces are
cones intersecting in K_s intersection K_t, so

    beta(E_e) = -beta(K_s intersection K_t).                                  (2)

Refine the original H-class to the pair/triple blocks of t, obtaining q_t.
Its complete original family has the H blocks fixed and outside family K_t;
the original separator formula, or directly the signed join definition, gives
kappa(q_t)=beta(K_t). Similarly refine H to the join of an edge's two matchings.
This is a noncrossing (2,4) split q_e. Its four-block has exactly the two
noncrossing pairings s,t; its pair-block is fixed. Thus kappa(q_e)=beta(E_e).
These are original-game coefficients, not conjectural compressed quantities.

The theorem winningJoinCoefficient_nonzero_crossed_min_five applies to ANY
pattern, including disconnected q_t and q_e. Consequently each of these
coefficients is zero if one of its new small blocks crosses an outside full
five-class. If no such crossing occurs, every outside certificate is compatible
with that whole boundary partition. In that case beta(K_t)=B or beta(E_e)=-B.

Call such states and edges universal, and let their numbers be u and v. Then

    kappa(p) = beta(P) - (u-v)B.                                              (3)

## 4. A nonzero source has no universal boundary certificate

For each outside FULL class, partition the six positions by which cyclic gap
of that class contains them. The meet R of these gap partitions is noncrossing.
A six-block avoids crossing every outside full class exactly when it lies in
one R-cell. Thus the universal states are exactly the 2/3 certificates refining
R, and the universal edges are exactly the (2,4) joins refining R.

H is crossed in a nontrivial NCConnected pattern, so R is proper. If R admits
any 2/3 certificate, it has no singleton cell, and its profile must be (3,3),
(2,4), or (2,2,2). The corresponding (u,v) are (1,0),(2,1),(1,0). If it admits
none, (u,v)=(0,0). Hence a universal state gives u-v=1 and A=A0; (3) then gives
kappa(p)=0. For the nonzero case under study we have, separately,

    beta(P)=kappa(p) != 0,
    beta(K_t)=0 for every t, and beta(E_e)=0 for every edge e.                  (4)

This separate vanishing is essential below; equality of aggregate sums alone
would not suffice.

## 5. Factoring the outside constraint system

Restrict to supported domains. A constant coordinate would make P a cone,
contrary to (4), so every coordinate has at least two values. Connect two
coordinates when their combined raw binary constraint is nonuniversal on these
domains. A factors as a Cartesian product over the connected components of
this graph. The choice complex is the join of the component complexes, so its
beta is the product of their betas. Every factor is nonzero.

In a component with two or more coordinates, each proper cut has a raw
nonuniversal edge, with a one-row / one-column cover. The existing theorem
choiceAlternatingSum_zero_of_covered_binary_spec therefore excludes three or
more assignments. One assignment would give constant coordinates. Thus such a
component has exactly two assignments, differing at EVERY coordinate. A
one-coordinate component has k>=2 assignments (one per supported value),
with beta=1-k.

Two full five-classes from different components cannot cross. Indeed a crossing
five/five relation has a row/column cover. On two domains of size at least two,
a covered relation cannot be universal. It would therefore create a component
edge. This is an ORIGINAL-position fact, and will let us extend assignments
that were not initially assumed supported.

## 6. There is only one outside component

If a six-state belongs to every supported row N_i(x), then K_t=P, contradicting
(4). Thus the common intersection of all supported rows is empty. By 2-Helly,
two such rows are disjoint. They must belong to the same component C: rows
from different components always intersect by their universal composed binary
constraint. In particular the intersection of all rows in C is empty.

C cannot be a one-coordinate component with >=3 values, by the three-row
common-state property in Section 1. Thus C has exactly two assignments a,b,
completely separated at its coordinates. Write D_C(a),D_C(b) for their boundary
lists. They are nonempty members of L and are disjoint.

Let U be the six-states occurring in ANY complete global certificate. There
cannot be an edge {s,t} with s in D_C(a) intersection U and t in D_C(b)
intersection U. To prove this, retain only C and H, refining H to the (2,4)
join of s,t. Consider ANY original local certificate for this smaller pattern.
Its H state is s or t. Since that state is globally supported, take a global
certificate with it, and use its outside coordinates off C. Classes on and off
C are uncrossed by Section 5, so the arbitrary local certificate extends to a
complete global certificate. Its C-assignment must therefore be a or b.
Disjointness of D_C(a),D_C(b) shows the smaller pattern has EXACTLY two
certificates, namely (a,s) and (b,t).

Their join is the smaller pattern: distinct five-states join to their full
five-class, and s,t join to the designated (2,4) split. Neither singleton
certificate equals the smaller pattern, so its coefficient is -1. Crossed-small-
class vanishing says neither distinguished small block crosses a full class in
C. But then BOTH s and t are compatible with EVERY local assignment on C,
contradicting the disjoint lists. This proves the asserted absence of edges.

Now fix any assignment c in another component C'. Fix assignments in all
remaining components. Cartesian factorization permits combining these choices
once with a, once with b; each global outside assignment has a six extension.
We obtain s in D_C(a) intersection U and t in D_C(b) intersection U, both
belonging to D_C'(c). They are distinct and not adjacent by the preceding
paragraph. The only list in L containing such a pair is the universal list.
Therefore D_C'(c) is all eight states, for every c. Each supported local row in
C' is consequently all-eight. Every coordinate has >=2 supported values, so
the full-row property from Section 1 implies that none of these classes crosses
H. They also cross no class in other components. This contradicts the original
class-crossing connectedness of p (equivalently its NCConnectedness). Thus C'
does not exist.

We conclude that A has exactly two assignments, separated in every coordinate.
This includes the single-five-class case: a one-coordinate family of >=3 values
would have a common six-state and violate (4). Hence beta(P)=-1.

## 7. The complete family has two or three members

Let the two outside assignments be a,b, and their nonempty fibres D_a,D_b.
A common state would give K_t=P, contrary to (4), so the fibres are disjoint.
An edge {s,t} between them would give E_e two disjoint choice facets, beta=-1,
again contrary to (4). Neither fibre can be universal. In K_{2,3}, two disjoint
edges have a cross-edge, and every matching vertex outside an edge is adjacent
to an endpoint of it. Thus the only possibilities are:

* two singleton fibres: two complete original certificates;
* one matching-edge fibre and one singleton TRIPLE fibre: three certificates.

This is a 16-list finite lemma in SixBoundaryLists.lean, independently checked
in check.py. The coefficient is already -1 from Section 6.

## 8. Every five-class is (1,2,2), also in the three-member case

Its two states have different pair blocks P,Q. If those pairs overlap, the
five-state catalogue provides a consecutive class edge in both triple blocks.
All original certificates contain that edge. Their join is p by nonzero
coefficient, so the common-gap theorem makes it globally adjacent. The family
that keeps the pair inside a triple is then the entire family. Its coefficient
is -1, contradicting the previously proved restricted adjacent-triple
cancellation for a five-class. Thus P,Q are disjoint.

Each pair is identified by both outside states, so common-gap adjacency makes
both global two-runs. The general five-class no-three-run theorem prevents
merging either with the singleton or with the other pair. This proves (1,2,2)
without assuming the full family has two members.

## 9. Three certificates force a six-class three-run

Write the three certificates as (a,T),(b,M),(b,N), where T is a triple state,
and M,N share an adjacent class pair P. Each of T joined with M or N is the
full six-class; the outside states also join fully. Thus both corresponding
pairs of ORIGINAL certificates join to p, and the common-gap theorem applies
to either pair separately.

If T preserves P, the finite six catalogue supplies two consecutive cyclic
class edges, each common to T and at least one of M,N. Common-gap adjacency
makes them consecutive edges of the whole board, producing a three-run.
There are twelve such cases, checked exhaustively.

If T splits P, rotation/reflection normalizes the states to

    T = 045 / 123,   M = 01 / 23 / 45,   N = 01 / 25 / 34.

The common edges 23 and 45 of T,M are globally adjacent, by their full join.
Let the four remaining open gaps, in cyclic order, be

    J=(0,1), K=(1,2), I=(3,4), L=(5,0).

There are no positions in (2,3) or (4,5). A block of the a-certificate, being
compatible with T, lies in one of I union J, K, L. A block of the b-certificate
is compatible with both M,N, hence with their noncrossing join 01 / 2345, and
lies in one of J, I, K union L. The implication to the join can also be seen
chordwise: compatibility with both matchings keeps every connected component
of their union on one side of every outside chord. These gap partitions can
be read directly from the two boundary partitions.

For a five-class, Section 8 gives a singleton root and two globally adjacent
doubled endpoints. The a-triple joins the root to one endpoint; the b-triple
to the other. Each doubled endpoint lies wholly in one of the four gaps.
If the root is in I or J, the full five-class lies in I union J and every
b-block lies in I alone or J alone. If the root is in K or L, the full class
lies in K union L and every a-block lies in K alone or L alone. This is the
eight-case finite star-switch lemma in SixBoundaryLists.lean.

Now choose b on every I/J class and a on every K/L class, and choose T on H.
Within either group these are the original noncrossing b or a blocks. Across
groups every block lies in a single one of four disjoint intervals, so no
crossing is possible. They all avoid T. This constructs an ORIGINAL complete
certificate, with a mixed outside assignment.

There must be a K/L class, since otherwise b itself would allow T, contrary
to D_b={M,N}. If there is also an I/J class, the mixed assignment differs from
both a and b, contradicting Section 6. Hence I/J classes are absent, so I and
J are empty. Together with adjacent 23 and 45 this gives a four-run 2345.
In particular it gives a three-run. The earlier inflation theorem then
excludes the four-run in a nonzero first-excess pattern. Thus the split case
cannot occur at all; the preserving case supplies the required three-run.

This replaces the FALSE assertion that pair-adjacency alone forces b to allow
T in the split case. Its concrete counterexample is retained in checks.json
and FAILURES.md. The new argument uses global two-assignment exhaustiveness,
all-five run shape, and an explicit mixed-certificate construction.

## 10. Counts and remaining problem

The prior complete two-generator search and complete three-run inflation
search are now exhaustive for first excess, by Sections 1-9. Their totals are:

| j | Length 5j+1 | Two certificates | Three certificates | Total |
|---|---|---|---|---|
| 2 | 11 | 0 | 22 | 22 |
| 3 | 16 | 88 | 224 | 312 |
| 4 | 21 | 2121 | 3486 | 5607 |
| 5 | 26 | 49725 | 67132 | 116857 |

All signs are -1. Thus the signed connected first-excess coefficient at
length 26 with five classes is -116857 at the combined paper/exact-computation
verification level. No new larger census was used in this work.

check.py regenerates every local matrix from original positions, checks every
composed relation, and tests (1)-(4) on ALL 5816 existing full-join length-21
representatives, including the zero-coefficient cases. The 142 nonzero
representatives comprise 59 two-certificate and 83 three-certificate cases.
That regression supports the proof and checks signs; it does not prove its
unbounded conclusion. The older complete counts and original-family replays
remain pinned by PR47 and PR48 receipts.

The full problem still requires arbitrary higher excess: profiles with a
seven-or-larger class, multiple six-classes, and their interactions. Their
boundary lists need not have this 2-Helly / covered-composition structure;
positive coefficients already occur. This report does not claim a full
winning-word formula, a polynomial algorithm, or a solution of A035617.

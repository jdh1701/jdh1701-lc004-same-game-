# Complete two-generator first-excess enumeration

2026-10-31, America/New_York. Based on PR47, receipt commit
093d3fba9ce9133b196cd36cd50c9cf96b69e23d.

## Result and scope

**PROVED-PAPER:** the common-gap argument gives an exhaustive compressed
enumeration of every nontrivial connected pattern of profile (6,5,...,5)
whose COMPLETE original certificate family has exactly two members and full
join. No six-class run-shape conjecture is assumed. Each such pattern has
original coefficient -1. The procedure applies to every number j>=2 of
classes; the supplied executable has finite index/counter limits and is
exhaustively run here only for j=2,...,5.

**VERIFIED-COMP:** the resulting two-generator counts are

| Classes j | Original length | Four-vertex six-core family | Six-vertex six-core family | Total two-generator patterns |
|---:|---:|---:|---:|---:|
| 2 | 11 | 0 | 0 | 0 |
| 3 | 16 | 80 | 8 | 88 |
| 4 | 21 | 1,974 | 147 | 2,121 |
| 5 | 26 | 46,930 | 2,795 | 49,725 |

The length-26 result extends this project's earlier complete two-generator
range. It is **NOT a complete first-excess census or an A035617 term**.
PR47 independently supplies 67,132 nonzero length-26 patterns with a unique
three-run and exactly three certificates. The two families are disjoint, so
their union has exactly **116,857** members. This gives a lower bound on the
full nonzero connected first-excess population. Its signed contribution is
-116857; this is not asserted to bound the full signed coefficient, because
additional families could have either sign.

The unresolved statement needed to finish this layer is: every nonzero
connected first-excess pattern without a three-run has exactly two original
certificates. The small complete censuses support it but do not prove it.
Even that result would leave arbitrary higher-excess families and the full
winning-word problem open.

No Lean files are changed here. PR47's supporting common-gap lemmas are
certified at source464f98e0996dfea5e9c79bb98bccfb0daa03521b, with247 modules
and4164 audited declarations. The present enumeration theorem is a paper proof,
and the finite counts have separate computational receipts.

**Final hosted verification:** source
b0b0288d68b1671fab092be9c638e203e149beca, run41223523261, job124602808734
completed/SUCCESS. All32198 positive original-family replays, all explicit
rotation unions, previous-census pattern-set comparisons and witness hashes
reproduce. The n26 stream agrees with the initial unfiltered discovery hash.
No Lean source changed from the supporting certified source. Full hosted log,
source hashes, the initial probe and exact scope are retained in receipts.json
and the adjacent archives. The final receipt commit changes documentation and
evidence only. PR35 remains at c88cc090, with no new proof to integrate.

## 1. Why the five-classes still compress

Suppose the complete original family is {c,d} and c join d=p. On every
five-class the restrictions are distinct pair/triple partitions. The proof
in PR47 does not require other classes to have size five once this family
hypothesis is supplied. If the local pair blocks overlap, their shared triple
edge is globally adjacent by the common-gap theorem. Restricted contraction
cancellation would give zero for its triple-family coefficient, whereas
{c,d} gives -1. Thus the pair blocks are disjoint. Each is identified by both
certificates, hence globally adjacent by the common-gap theorem. The general
five-class no-three-run theorem from PR46 makes the runs exactly (1,2,2).

Accordingly each five-class becomes a three-vertex weighted star, exactly as
in PR47. This deduction is conditional on the COMPLETE two-generator family;
we do not assume or claim it for arbitrary first-excess survivors.

## 2. Compress only forced edges of the six-class

A noncrossing 2/3 partition of six positions is one of five three-pair
partitions or three two-triple partitions. Enumerate every unordered pair
of these eight states whose join is the whole six-class: there are22.
The explicit finite catalogue in preparation.json shows that such a pair
identifies either zero or two cyclic consecutive class edges in common.
In the latter case these two edges are disjoint.

Each shared edge is globally adjacent by the common-gap theorem. Contract
exactly those two edges; retain the other two positions as weight-one vertices.
The six-class then has four vertices, of weights2,2,1,1 in the appropriate
cyclic order. With no shared edge, retain all six positions with weight one.
Other adjacent occurrences of the six-class are deliberately allowed. They
are not silently contracted or excluded by an unproved run-shape rule.

For every original local pair, `prepare.py` forms the forced clusters, rotates
their cyclic order in every way, and canonically normalizes the two local
partition labelings. Interchanging the pair is normalized lexicographically.
Deduplication gives17 compressed local types: ten on four vertices and seven
on six. Expansion is checked back against the complete original catalogue.
All22 original full-join pairs are retained in the preparation record.

The unique six-class distinguishes this local orientation: choose the smaller
local state as upper, the other as lower. Every five-star retains both
orientations. Thus global exchange of c and d creates no duplicate.

## 3. Exhaustive construction and exact acceptance

For each compressed local type with k=4 or6 vertices, use m=3(j-1)+k positions.
Enumerate every k-subset for the unique six-class. Partition the remaining
positions into triples by repeatedly taking their smallest unused element.
Choose each triple's root and both upper/lower orientations. Forbid adjacent
equal five-class vertices, since their original maximal runs are (1,2,2).
Allow all six-class adjacencies. Remove only same-layer crossings while
constructing the pair. Every original two-generator source compresses to a
visited candidate, and expansion preserves noncrossingness of the pair.

At a leaf, require the original class-crossing graph to be connected.
The raw directed incompatibility graph of the chosen two local states gives
a necessary SCC filter: if it is not strong, a nonempty proper outgoing-closed
set lets us switch from upper to lower on exactly that set and obtain a third
valid original certificate. This contradicts a complete two-generator family.
The filter therefore cannot remove a desired pattern.

SCC is NOT used as sufficient acceptance. For every remaining candidate the
program expands all weights, generates all original five- and six-state local
choices, and enumerates the COMPLETE original certificate family. A third
certificate rejects the candidate. Exactly two are required. They have full
join by the construction of each local pair, giving original coefficient -1.

Every accepted original pattern has an intrinsic unordered certificate pair,
intrinsic five-class runs, and intrinsic forced six-class edges. Consequently
compression is inverse to expansion on these accepted decorated objects.
No pair-search multiplicity remains after complete-family acceptance.

The executable also runs with the SCC filter disabled. The entire positive
witness streams are byte-for-byte equal through j=4. The initial j=5 discovery
run likewise omitted that filter; its witness hash and the final filtered
run agree. SCC is an optimization, not a changed definition of the objects.

## 4. Root counts without assuming trivial stabilizers

Let N_(j,k) be the accepted compressed count on m=3(j-1)+k labeled circular
positions. The contraction retains an intrinsic weighted decomposition and
the unordered original certificate pair, so it preserves the order h of every
cyclic stabilizer. A core orbit has m/h rooted representatives; its expanded
source has (5j+1)/h. Therefore, for each k separately,

    T_(j,k) = (5j+1)/(3(j-1)+k) * N_(j,k).

This handles rotations that interchange the two original certificates: they
act on unordered pairs, and the lexicographic local representative is simply
renormalized. No free-rotation assumption is introduced.

At j=5, N_(5,4)=28880 and N_(5,6)=1935. Thus
26*28880/16=46930 and 26*1935/18=2795. Explicitly expanding every accepted
core and taking the union of all normalized original rotations independently
checks both the total count and absence of duplicate weighting through j=5.

## 5. Verification and boundaries of independence

`replay.cpp` consumes original position words only. It does not read the
compressed types or SCC graph. It regenerates all local partitions by
restricted-growth strings, discards every block outside sizes2/3, and filters
crossings by inside/outside counts. The search instead loads the independently
derived recursive-interval catalogues and tests alternating endpoints.
The replay enumerates every original certificate, requires exactly two,
checks their join on every color class, and checks original connectivity.
It also records run shapes, which are observations rather than acceptance
assumptions about the six-class.

Every positive compressed witness through j=5 is replayed this way.
The construction/acceptance code and the replayer share the mathematical
pairwise-compatibility reduction and smallest-domain search strategy; they
are not independent at that conceptual level. They have separate catalogue
generation and geometric crossing implementations. Completeness relies on
Sections1-4, not only successful positive replay.

The explicit positive pattern sets agree with the earlier COMPLETE first-excess
censuses at n16 and n21 after selecting their two-generator strata. This is
a different enumeration strategy, not merely a numerical checksum. A sample
from every represented local type is also checked by the older Python original
certificate/signed-join implementation. Full witness streams are regenerated,
hashed and replayed; small samples are retained in the repository.

All accepted six-classes through j=5 have run shapes (1,1,2,2) or (1,1,1,1,1,1).
Some of the17 theoretically possible compressed local types have no accepted
objects in this range. Neither observation is promoted to a uniform theorem.
In particular, the program did not preselect these two shapes or prune those
empty types. The complete-family test, not a presumed classification, rejected
their candidates.

Reproduce:

    python research/two_generator_excess_20261031/check.py

The full problem remains OPEN. The next finishing obligation is the no-three-run
first-excess two-generator theorem, not another count extrapolated from this table.

# Beyond first excess: a seven-class has exact ternary elimination

This is a follow-on to the uniform first-excess paper proof in PR49. It is a
new reduction and two retained obstructions, NOT a higher-excess classification
or a solution of LC004/A035617. No new large census is attempted.

## What survives uniformly

For one seven-class H and arbitrarily many five-classes, the local catalogue
has 21 noncrossing 2/3 certificates, each with three blocks. The 792 five/seven
order types give 338 distinct compatibility matrices. Their row sets form an
intersection-closed family of 37 lists:

* the empty set and all 21 states;
* 21 singleton lists;
* seven two-state lists, corresponding to noncrossing (3,4) coarsenings;
* seven five-state lists, corresponding to an adjacent pair plus its five-point
  complement, i.e. a noncrossing (2,5) coarsening.

These lists are **3-Helly, but not 2-Helly**. This is an unbounded statement
about the number of lists, with the following finite proof. A minimal empty
family containing a list of size at most two has at most three members: for
each of its at most two elements choose a list excluding it. Any larger
minimal obstruction would therefore use only the seven five-state lists
(the universal list cannot matter). All 128 subfamilies of those seven are
checked: if all subfamilies of size at most three intersect, the entire family
intersects. The explicit three-list obstruction proves the bound is sharp.

Consequently eliminating H from the original complete family is exactly
specified by the original five/five compatibility, plus nonempty intersections
of the selected boundary lists for every subset of at most THREE coordinates.
This works for any number of five-classes. It extends the six-class elimination,
which needed only pairs, but does not provide the earlier binary cancellation.

## Boundary-list classification does not require outside classes of size five

There is a useful structural strengthening of the finite row checks. For ANY
noncrossing outside certificate, partition the distinguished H positions by
which cyclic gap of each outside block contains them, and take the meet R of
these gap partitions. R is noncrossing. An H certificate is compatible with
those outside blocks exactly when it refines R.

If R has a singleton cell, no 2/3 certificate refines it. Otherwise, for six
points a proper R has profile (3,3),(2,4), or (2,2,2), giving a singleton or one
of the six two-state lists in PR49. For seven points the possible proper
profiles are (2,5),(3,4),(2,2,3), giving the lists described above. If R is top,
the list is universal. Thus the SIX-point 2-Helly and SEVEN-point 3-Helly
extension criteria apply to local certificates of arbitrary outside class
sizes, not only to five-classes. The majority and cover properties needed for
PR49's later cancellation remain specific additional hypotheses.

The six-point Euler elimination also has an arbitrary-profile form. Replace
the outside choice complexes by their FULL original local-separator complexes.
The six-cut incidence, refined-pattern corrections and crossed-small-class
vanishing from PR49 still apply verbatim. For a nontrivial NCConnected pattern
with one distinguished six-class, if a six-certificate avoids every outside
FULL class, its coefficient is zero; otherwise its coefficient equals beta of
the union of the projected outside separator facets. This follows from
kappa=beta(P)-(u-v)B, with u-v either zero or one, and P=P0 whenever a universal
six-state exists. No all-five assumption is needed for this Euler identity.
This is a paper extension, not a new Lean theorem or a higher-profile census.

## Two shortcuts fail

Of the 338 squared composed pair relations, 278 are not conservative-majority
closed. More importantly this failure occurs in an ACTUAL original (5,5,7)
family, not only in an unrealizable pair of raw matrices. The pattern

    1 1 0 0 0 2 2 0 0 2 1 1 2 2 1 2 2

has outside projection containing (4,0),(4,3),(2,4), but not (4,4). The
coordinate operation m(x,y,z)=x if x=y, else z maps those three inputs to the
missing tuple. The complete family is enumerated and retained in checks.json.
Its coefficient is ZERO: this example does not disprove a future closure
statement with a nonzero-coefficient hypothesis.

Pairwise boundary intersections also fail to guarantee extension even when
the chosen outside certificate blocks are mutually noncrossing. An explicit
(5,5,5,7) pattern and outside assignment in checks.json give the three lists

    {0,1,2,3,4}, {2,5,12,14,17}, {4,10,12,16,19}.

Every pair intersects, while the triple intersection is empty. In that example
the whole original family is empty. This is a counterexample to the raw binary
specification, not a claim about exact pair projections of a nonempty family.
All state numbers in this folder use core.py's catalogue order, recorded in
checks.json; they must not be confused with the Lean six-state order.

A stronger targeted search then found a NONZERO original counterexample:

    0 2 2 0 1 1 2 2 1 2 2 1 1 0 0 2 0.

Its class-crossing graph is connected, its profile is (5,5,7) in numeric color
order 0,1,2, and its complete original family has exactly seven certificates.
The coefficient is +1, independently checked by the original signed-join
calculation. Its outside projection has beta=+1 (a single cycle with trees
attached), and every Euler correction below vanishes separately in this
example. Its outside projection contains (3,0),(3,2),(1,1), but not (3,1),
again violating majority closure. The complete choices and witness are saved
and regenerated by check.py. Thus even a NONZERO coefficient hypothesis cannot
restore projected majority closure beyond first excess. This example was found
at trial 37847 of a fixed-seed search (seed 20261101); discovery statistics are
not completeness claims and are unnecessary to the exact counterexample proof.

## An exact Euler reduction to a ternary projection and all-five coefficients

For the projected outside family let P be its ordinary choice complex, and
K_t the subcomplex of outside assignments allowing seven-state t. Let beta be
the alternating face sum including the empty face. For each nontrivial local
cut c let E_c be the ordinary choice complex with an extra coordinate whose
values are the states refining c, together with their allowed outside tuples.

The seven-state cut facets each have three vertices. Any two distinct facets
share at most one vertex. There are fourteen cut vertices contained in only
one facet, seven contained in five facets, and seven contained in two facets.
The last fourteen are exactly the noncrossing (2,5) and (3,4) coarsenings.

The same inclusion-exclusion used in PR49, now grouped by the unique shared
cut of any two or more local states, gives the uniform identity

    kappa(p) = beta(P) - sum_{t=0}^{20} beta(K_t)
                       - sum_{seven (2,5) cuts c} beta(E_c)
                       - sum_{seven (3,4) cuts c} beta(E_c).

For clarity, the ordinary choice complex E_c is a union of cones, one over
each K_t. Its beta is the sum of the inclusion-exclusion terms of size at
least two; singleton cone terms are zero. Since no pair of state facets
shares two cuts, every correction of size at least two occurs in exactly one
E_c. Singleton corrections supply the separate sum of beta(K_t). This proves
the displayed formula without assuming intersections of face complexes are
complexes of common full assignments.

All corrections are ORIGINAL coefficients of refined patterns:

* beta(K_t) refines H to its fixed pair/pair/triple certificate.
* A (3,4) correction refines H to its triple and four-block; the latter has
  exactly the two noncrossing pairings. This is the extra two-value coordinate.
* A (2,5) correction refines H to its pair and five-block; the latter has the
  five original local certificates. This is the extra five-value coordinate.

Crossed-small-class vanishing kills the first two kinds whenever a small
refined block crosses an outside full class. If all those blocks are uncrossed,
they reduce to the outside all-five coefficient B and -B respectively.
For a (2,5) correction, a crossed distinguished pair also kills the term.
If that pair is uncrossed, it is a separate noncrossing component of weight 1;
what remains is an entirely ALL-FIVE pattern, computable by the previously
proved all-five law and noncrossing component factorization. Thus every Euler
correction is already reduced to all-five coefficients. The outstanding new
quantity is beta(P), for the exact ternary constraint system above.

This is a concrete next proof target, not a completed evaluation of beta(P).
In particular, discarding the (2,5) corrections would be wrong: the newly
created five-block can cross other five-classes and have a nonzero coefficient.
That is precisely where the six-class argument's separate vanishing stops.

## Verification scope

check.py regenerates all 792 order types, all 114244 composed relations, the
37-list Helly argument, all three realized obstructions, and the full seven-cut
incidence. The new Euler identity is checked on every 5/7 order type, with
672 crossed cases also compared directly against original signed-join
calculation (complete families of at most 12 generators). The replay bound
is only a finite regression budget, not a premise of the uniform identity.

This folder has no new Lean theorem. Its status is a computer-assisted paper
reduction plus exact finite checks. The new ternary system's nonzero Euler
classification, multiple six-classes, and arbitrary higher excess remain open.

Hosted exact verification passed at source b67d938aeed992c06aeaf7f975ac827f8b30d0da,
run 41267556436, job 124733423229. The log and hashes are retained in
receipts.json. The Lean source and audit scripts are byte-for-byte unchanged
from PR49's audited formal source 80e6c8dc3df62ada6721b0b8544cecace24b9d1c.

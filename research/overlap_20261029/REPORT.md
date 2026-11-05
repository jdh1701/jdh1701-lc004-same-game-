# Certificate overlap and cancellation campaign

Baseline prior CI 40936230765 succeeded at eb24cd4902365171ff555b7e1cf159319fef7f9e.
This checkpoint extends the cross-domain experiments; no new Lean result.

VERIFIED-COMP: all 456 crossed partitions of profile (6,6), n=12: 426 have
coefficient zero, 30 have coefficient -1. Exact signed certificate-join
aggregation used; four collision witnesses independently verified by raw-game
Mobius inversion over all local refinements.

KILLED: even at fixed class profile, certificate count determines coefficient.
Explicit examples with two certificates, respectively coefficient 0 and -1:
000010111011 and 001011001011. Complete unambiguous array representations
are in verification.json (use these as authoritative over typography).
Four-certificate witnesses also collide.

VERIFIED-COMP: construct graph G with certificates as vertices; an edge means
the pair's join is the target pattern. For every tested (6,6) pattern, I(G,-1)
agrees with the coefficient, with the separate zero-certificate convention.
This is a different graph from the class crossing graph previously refuted.
KILLED: every generating certificate subset contains a generating pair.
There are 26 (6,6) patterns with minimal generating triples, witnesses higher.json.
Thus equality of alternating sums, when it holds, needs a cancellation argument,
not equality of the underlying families. Pair-edge counts/degree sequences have
no coefficient collisions in this finite profile; no universal claim follows.

## Exact finite identity (PROVED-PAPER, not new prior-art claim)

Fix a nonempty finite family C of certificates refining p. Assume the signed
join formula for c(p), already available in Lean. Let K be the simplicial
complex of subsets S of C whose join is strictly below p. If the empty join
is below p (as in all profiles tested), then
  c(p) = sum_{S in K} (-1)^|S| = - reducedEulerCharacteristic(K).
Proof: the sum over all subsets is (1-1)^|C|=0. Split into generating and
nongenerating subsets and negate the generating part. The signed-join formula
identifies that negated sum with c(p). The empty certificate-family case is
separate and has coefficient zero for nonbottom p.

K is contained in Ind(G), the graph independence complex. Missing faces are
exactly independent subsets whose join is nevertheless p. Therefore
  I(G,-1)-c(p) = sum_{S in Ind(G), join(S)=p} (-1)^|S|.
This gives a precise target: pair the missing faces by opposite parity while
preserving their generating and pair-independent properties, or find an
uncancelled obstruction. It does not assume the pair-graph identity universally.

## Next/Claude handoff

Use explicit minimal triples to test a relative discrete Morse matching on
Ind(G) minus K. Preserve the full certificate incidence data, not only class
crossings, genus, certificate count or vertex degrees. The prior redundant-atom
cone attempt is already known insufficient. A relative matching can be weaker
and local; successful matching must be proved for every face, including boundary
cases. The (6,7) holdout is selected with fixed seed before inspection.
No direct Claude invocation, new Sage computation, or new Lean build occurred.

## Holdout refutation and revised target

KILLED: c(p)=I(G,-1) universally for the certificate pair-generation graph.
The 60-pattern (6,7) holdout has two mismatches, each actual coefficient +2
versus graph prediction +1. Both actual coefficients were independently verified
by raw-game Mobius inversion. This also kills the universal assertion that all
missing faces admit a complete parity-reversing matching.

VERIFIED-COMP: correction.py explicitly enumerates every subset of the 9 and
12 certificates in these witnesses. It isolates independent generating subsets
and verifies that their alternating sum is -1 in each case. Full face counts
by size are in correction.json. Thus the exact identity above explains the
one-unit discrepancy, without fitting or an assumed graph formula.

Revised next target: retain higher-order minimal generating hyperedges, or find
a relative Morse reduction with explicitly enumerated unmatched critical faces.
A graph-only universal cancellation theorem should not be pursued. The full
independence complex of the minimal-generator hypergraph is exact by definition;
the unsolved task is to compress/enumerate it without exponential subset work.
Do not mistake this reformulation for a solution or a novelty claim.

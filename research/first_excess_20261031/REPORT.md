# First-excess n21: complete census and a failed recursive reduction

2026-10-31. The all-length Same Game counting problem remains open.
This is exact finite enumeration of connected coefficient patterns, not a new
winning-word sequence term and not an all-length theorem.

## Reconciled verification and related work

PR43 source 9656d7b90554fb736388e6c14d92f2d73060e470 is now fully PROVED-LEAN:
run 41099342084 reports both exact job 124213324550 and Lean job 124213325344
completed/SUCCESS. The previously pending API metadata is resolved. The proof
closure contains 243 modules and 4082 audited declarations, standard axioms only.
This continuation changes no Lean files and makes no additional Lean-proof claim.

PR35 advanced to 352d5b54e96943f1f0b3c63ff05ad301a9d8fd58. The intervening
changes review PR42/43 and independently check n11. They introduce no new Lean
source requiring integration. Its phrase about 22 NCConnected (5,6) patterns
must be read as NONZERO patterns: our complete control has 451 connected
patterns, 429 with coefficient zero and 22 with coefficient -1. The profile
support theorem never claims that all connected patterns in the profile survive.

## Complete n21 result

There are choose(21,6)*15!/(5!^3*3!) = 6,844,101,264 patterns of profile
(5,5,5,6). Exactly 5,607 connected patterns have nonzero original coefficient;
all have coefficient -1. Thus connectedClassCoefficient(21,4) = -5607, using
the existing general first-excess support theorem. This finite equality is
VERIFIED-COMP, not a Lean-certified numeral evaluation.

| Quantity | Exact count |
|---|---:|
| All profile patterns | 6,844,101,264 |
| Six-subset dihedral orbits | 1,353 |
| Template completion cases tested | 18,069,315 |
| Patterns with certificates | 56,506,226 |
| Connected patterns with certificates | 53,433,226 |
| Connected patterns with full certificate join | 206,290 |
| Nonzero connected patterns | 5,607 |
| Two-generator survivors | 2,121 |
| Three-generator survivors | 3,486 |
| Sum of connected coefficients | -5,607 |

## Exhaustiveness and weighting argument

The six-point class is unique. Its subsets split into explicitly constructed,
disjoint dihedral orbits with total weight choose(21,6)=54264. For each chosen
representative, enumerate EVERY partition of the remaining fifteen ordered
positions into three five-classes. Canonical minimum-element ordering gives
126126 templates without duplication. Exactly 13355 templates admit a
certificate, with 60060 total certificate incidences. A full certificate must
restrict to a certificate of its template, so omitting infeasible templates
cannot remove a nonzero coefficient.

For each feasible template, all its complete assignments are extended by each
of the eight six-point local certificates and tested for pairwise block
noncrossing against all three five-classes. Connectivity uses repeated crossing
merges of original class masks. All proper-full-join cases have coefficient
zero: no subset can join beyond the join of the complete family.

The remaining coefficients use exact signed subset-join dynamic programming
on 7^3*16 local join states. No sign, generator-count bound, run shape, or
inflation assumption is used to prune this search. Signed 64-bit intermediates
are checked below 2^50 after every update, making the next subtraction safe.

Multiply each completion count by the orbit size of its SIX-SUBSET. There is
no division by four because the six-class is already distinguished uniquely.
The subset stabilizer can permute completions, so a completion's full pattern
orbit may exceed its six-subset orbit. This distinction caused and corrected
an independent replay assertion; the census weighting was unchanged. See
FAILURES.md. Expanded positive pattern orbits have union cardinality 5607,
independently confirming the weighted survivor total.

A second exhaustive combinatorial checksum counts all certificate-pattern
incidences. For three-pair six-classes, there are six pairs and three triples;
for two-triple six-classes, there are three pairs and five triples. The count is

    21!/(13!*6!*3!) * choose(6,3)*3!
    + 21!/(14!*3!*5!) * choose(5,2)*3! = 276746400.

The program accumulates this number independently from every accepted full
certificate assignment and asserts equality.

## Independent replay and its limits

replay.py checks ALL 5816 full-join completion representatives using the
separator Euler sum with a different crossing test and coefficient algorithm.
5674 evaluate to zero and 142 to -1. It additionally regenerates complete
original certificate families and evaluates their original signed joins for
every positive representative. It explicitly expands all positive dihedral
orbits and checks the union count against the weighted total. structure.py
checks every positive representative's connectivity by enumerating proper
coarsenings, independently of crossing merges.

These are independent coefficient/positive checks, NOT a second independent
full census. Exhaustiveness still rests on the template/orbit construction.
The local catalogues and several existing utility definitions are shared and
credited by explicit imports; this is not claimed to be independent evidence
at every dependency. Hosted exact replay is recorded separately in receipts.json.

## Structural discrimination

Every surviving five-class still has cyclic run lengths (1,2,2).

| Six-class run lengths | n16 survivors | n21 survivors | Generators |
|---|---:|---:|---:|
| (1,2,3) | 224 | 3486 | 3 |
| (1,1,2,2) | 80 | 1974 | 2 |
| (1,1,1,1,1,1) | 8 | 147 | 2 |

Contracting the unique three-run in the n21 three-generator family recovers
exactly 415 all-five n20 survivors, matching the earlier independently checked
complete n20 count. Inflating every eligible two-run of these 415 parents and
taking the rotation-closed image gives EXACTLY the entire 3486-pattern
three-generator family, with equality of explicit pattern sets. Its size is
2*21*415/5 = 3486, as predicted by the earlier conditional orbit theorem.
The two-generator cases are exactly the remaining 2121 patterns.

The tempting alternative recursion, deleting some whole five-class to obtain
a smaller connected nonzero first-excess pattern, FAILS: 72 of 312 n16
survivors and 714 of 5607 n21 survivors have no successful five-class deletion.
At n21 this includes 588 three-generator and 126 two-generator survivors.
Explicit n16 witnesses and all n21 deletion sets are preserved.

Supported next targets are a uniform run-shape theorem, a proof of inflation
preservation, and an enumeration of the two-generator families. The computations
support but do not prove uniformity. A deletion grammar must allow intermediate
zero-coefficient states or richer boundary information; survivor-only deletion
is already falsified. Neither the first-excess layer nor higher excess is solved.

## Reproduction

    python research/first_excess_20261030/prepare.py
    python research/first_excess_20261031/prepare.py
    g++ -O3 -std=c++17 -Wall -Wextra -Werror research/first_excess_20261031/count.cpp -o /tmp/count5556
    /tmp/count5556 research/first_excess_20261031 research/first_excess_20261030/tables.txt > research/first_excess_20261031/count.json
    python research/first_excess_20261031/replay.py
    python research/first_excess_20261031/structure.py

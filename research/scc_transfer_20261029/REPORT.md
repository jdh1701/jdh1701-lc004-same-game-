# Independent transfer/SCC enumeration: 415 and 6455

VERIFIED-COMP: the new program computes 415 at n=20 and **6455 at n=25**.
These count connected all-five patterns with exactly two noncrossing pair/triple
certificates whose join is the original pattern. They are not A(25,5), not the
full winning-word count, and not a general counting formula.

All128 completed shards of Claude's run40942806037 independently sum to415
and6455. Its source56d867dd07e781fe1565e8ab3761bb1c647e3009 was inspected and
preserved under claude_reference: it enumerates NC certificates, matches their
pairs to triples, counts actual atoms up to3, checks the partition join, and
selects the smaller atom to avoid duplicates. This genuinely ran n25, unlike the
older smoke run. All128 job outputs were retrieved, mathematical notices parsed,
and unique shard coverage0..127 checked for both n20 and n25. The audit JSON
retains every job id and count. The new method did not use6455 as an input.

## Why the new enumeration is exhaustive

A class is a five-element set of positions. Choose one class G as distinguished.
The remaining classes form a partition of its complement. Order-preserving
compression of the complement means their local compatibility and feasible split
tuples depend only on the corresponding smaller rank pattern.

We enumerate all126126 three-class patterns on15 ranks and keep the13355 with
at least one certificate, together with all their60060 certificate incidences.
Appending a canonical first class on20 ranks generates exactly3769195 feasible
four-class templates and16279200 certificate incidences. A full solution cannot
have an infeasible restriction, so discarding infeasible templates loses nothing.

The incidence totals are independently predicted by

    (5j)! / ((3j+1)! j!),

obtained by counting NC partitions with j pairs and j triples and matching those
pairs to triples in j! ways. At j=3 and4 this gives60060 and16279200, both asserted
by the program. Template classes are ordered by their least position, so each
unlabelled template occurs exactly once.

For the distinguished five-set, prepare.py explicitly partitions all five-subsets
into disjoint dihedral orbits:406 orbits of total weight15504 at n20, and1096
orbits of total weight53130 at n25. Noncrossing and the surviving-pair property
are invariant under rotations/reflections. For every representative, append each
feasible template and use two searches plus the raw-constraint SCC criterion
(PROVED-LEAN, proof commitc365c2ae..., CI40984245009 success).

If H(G) is the number of surviving completions of G, the count is

    (1/j) sum_G H(G)
      = (1/j) sum_orbit_representatives_G |orbit(G)| H(G).

The divisor j comes from marking one of j classes, not from assuming that pattern
orbits have full size. Orbit stabilizers are handled by their actual cardinalities.

At n20,5422130 feasible-template completion cases give weighted sum1660, hence415.
At n25,4131037720 cheap template cases yield22743 tested candidate pairs and
weighted sum32275, hence6455. Most cases fail a local compatibility mask immediately.
The recorded local n25 computation took about63 seconds after compilation;
this is a single-environment measurement, not a controlled speedup factor.

## Independent positive checks and limits

All767 positive marked orbit cases at n25 were exported with the actual position
classes and both certificates. A separate Python implementation recomputes all
certificates using its own run-alternation crossing test, without the C++ table
or graph. Every case has exactly the two reported certificates, they differ in
every class, and their signed join coefficient is-1. The weighted witness sum
is32275. Every rejected candidate in C++ constructs and checks a third certificate.

The independent positive replay does not by itself prove absence of false
negatives. That rests on exhaustive template/orbit coverage, the complete two-search
criterion, the Lean recognition theorem, and agreement with Claude's entirely
different128-shard certificate enumeration. The finite enumeration and symmetry
weighting are not formalized in Lean. The original CertificateConstraint-to-split
bijection and winningJoinCoefficient/face-sum identity remain formal obligations.

CI scc-transfer.yml rebuilds both programs, regenerates the orbit cover, reruns the
full n20/n25 computations, independently replays all witnesses, and checks the
Claude shard sum. It uses no unbounded graph/CSP library or floating-point count.
Floating-point output is only elapsed time. Exact pins are in the follow-up
research/SCC_TRANSFER_CI_RECEIPTS_20261029.json.

## Research consequence

The verified support sequence for j=2,3,4,5 is5,35,415,6455. This gives a new
independently checked finite target and an efficient survivor filter for further
work. It does not supply a recurrence or solve the mixed-profile kernels.
A brief exact-number web search found no relevant match; that is not novelty
evidence. Primary meandric/free-cumulant leads and failed OpenAlex access are
recorded separately in research/FIVE_ACTUAL_LITERATURE_20261029.md.

# LC004 post-theorem adversarial research checkpoint

Date of this execution: 2026-09-23 UTC. Historical prompt/checkpoint: 2026-09-22.
Public verifier: `jdh1701/jdh1701-lc004-same-game-`, default-branch commit
`a9cb335c11b795372b7a4d22b68c6c4fab83239c`.
Recovered research source: private `jdh1701/alexandria-omega`, branch
`ancient-languages-master-dossier`, tree `63199b95ee24c79d7502549dbc37e16a5ac45c57`.
The original ordinary-word implementation is
`alexandria_omega_x/lc004_same_game.py`, blob
`3965d82eb9330438ec6228579b0ca6f5b69ddc7a`.
The present executable census uses the public repository's
`scripts/exhaustive_verify.py` transition implementation and separately
checks the recovered ordinary-word counts.

## Verified theorem

`LC004/UnconditionalFinal.lean` states that for normalized nonempty Boolean
run states, exactly one successful first indexed deletion is equivalent to
exactly one complete successful indexed path. The public repository records a
clean root build and standard Lean foundational axioms only; this checkpoint
inspected the theorem statement and reran the Python regression, but did not
independently rebuild Lean. The theorem is about its stated RunState model.
No q≥3 enumeration formula follows from it.

## Ordinary-word census and controls

Universe: all `q^n` ordinary length-`n` words over **labeled** colors
`0,...,q-1`. `W` is the count solvable by deleting maximal equal-color runs
of size at least two, `U` is the count with exactly one successful indexed
first move, and `B=W-U`. The empty word is excluded below; it is winning but
has zero first moves. Every ratio is within the same labeled-word universe.

| q | n | total | W | U | B | U/W | B/W | first-move arity 1,2,... | canonical B states | local pair signatures |
|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|
| 2 | 15 | 32768 | 25778 | 2278 | 23500 | 8.84% | 91.16% | 2278,5854,4350,7280,5086,900,30 | 836 | 78 |
| 3 | 10 | 59049 | 7833 | 1209 | 6624 | 15.43% | 84.57% | 1209,3468,2340,768,48 | 279 | 230 |
| 3 | 11 | 177147 | 23697 | 2709 | 20988 | 11.43% | 88.57% | 2709,9384,7908,3240,456 | 787 | 357 |
| 3 | 12 | 531441 | 71385 | 6057 | 65328 | 8.49% | 91.51% | 6057,24792,24810,12534,3096,96 | 2139 | 517 |
| 3 | 13 | 1594323 | 216765 | 13521 | 203244 | 6.24% | 93.76% | 13521,64470,76218,45660,15540,1356 | 5938 | 579 |
| 4 | 10 | 1048576 | 39244 | 4636 | 34608 | 11.81% | 88.19% | 4636,16680,13368,4236,324 | 442 | 354 |
| 4 | 11 | 4194304 | 142432 | 11980 | 130452 | 8.41% | 91.59% | 11980,52728,54168,20856,2700 | 1462 | 586 |

The full table for all computed `q,n`, legal-first-move distribution, exact
path counts grouped into 1–100 versus >100, and bridge/no-merge move totals
is in `results/census_compact.json`; `results/census.csv` is flat. Canonical
B states identify Boolean run sequences up to color relabeling and reversal,
while their source words remain separately counted with multiplicity.
The local pair signature records capped distance (4 means ≥4), color/weight
pattern in the union of one-run neighborhoods, endpoint flags, and whether
each selected move bridges. It is deliberately coarse; distinct signatures
are **not** grammar nonterminals, and a plateau can be caused by the cap.

The recovered source independently reproduced W counts through n=10:
q=2 `1,0,2,2,6,12,26,58,126,278,602`;
q=3 `1,0,3,3,15,33,105,297,879,2631,7833`;
q=4 `1,0,4,4,28,64,268,844,3100,10876,39244`.
The first two agree with OEIS A035615 and A035617; the extended ternary
count at n=13, 216765, agrees with A035617, and q=4,n=11 agrees with
Kurz's published polynomial. The public exhaustive
regression passed 797,161 ternary raw words through n=12 and 524,286
normalized ternary run states through nine runs, with zero reported
correspondence and uniqueness mismatches.

The approximate ten-percent criticism is **directionally correct but cannot
be stated as a universal percentage**. At q=3,n=13, U/W is 6.24%; the ratio
changes substantially with n and q. Full canonical B-state counts for q=3
rise 279,787,2139,5938 at n=10–13. Local signature counts rise
230,357,517,579. This finite range does not show the stable small motif
system needed for a recurrence. It also cannot prove indefinite growth.
Pair interaction distributions and the precise signature definition are
preserved in `results/pair_geometry_summary.csv` and `census.py`.

An additional ordered-pair transport test tracked each of two distinct
successful original runs across deletion of the other. At q=3,n=13,
653436 of 742824 pairs (87.97%) admitted both orders and reached exactly
the same Boolean state after two moves; 89388 (12.03%) were adjacent
critical pairs in which one original run was absorbed by the other's
bridge merge. At q=4,n=11 the respective counts were 335640 of 367368
(91.36%) and 31728 (8.64%). No surviving-run pair had unequal two-step
states in this finite census. These are **pairs of successful first moves
across labeled ordinary words**, counted with multiplicity, not distinct
states or complete paths. They suggest testing a commutation-quotiented
path representation, but do not give a counting recurrence. Exact distance
and interaction counts are in `results/pair_interactions.csv`, with the
index-transport convention in `pair_interactions.py`.

## Ordinary semantics and a counterexample to an overstrong statement

The public Lean files already define `RawState`, `encode`, and prove
`encode_normalized`, but do not prove ordinary deletion commutes with
`stepAt`. Independent ordinary-cell and Boolean-state implementations
agreed for q=2 through n=16 (131,071 words, 491,520 legal edges), q=3
through n=12 (797,161 words, 1,948,617 edges), and q=4 through n=10
(1,398,101 words, 2,359,296 edges), also on exact deletion-path counts.
The singleton bridge `0110 → 00` works as expected. This is finite evidence.

The tempting pointwise statement
`OrdinaryStep w i w' ↔ IndexedStep (encode w) i (encode w')` is **false**:
`w=0011`, `i=0`, `w'=111`. The actual ordinary successor is `11`, but
`11` and `111` have the same Boolean encoding. This refutes the displayed
iff, not the quotient correspondence. The correct Lean target is the
functional commuting equation
`Option.map encode (ordinaryStepAt w i) = stepAt (encode w) i`,
followed by existential relational correspondence and path transfer.
No claim that this equation is Lean-proved is made here.

## Biedl grammar versus path ambiguity

Biedl et al., *The Complexity of Clickomania*, §2.2,
https://arxiv.org/pdf/cs/0107031, give
`S → ε | SS | cSc | cScSc` for each color c and prove language equivalence
with solvable ordinary words. Literal parse-tree count `G(w)` is infinite
for every accepted word because `SS` can insert an empty child repeatedly.
After explicitly forbidding empty children only in `SS`, the first
substantive discrepancies occur at n=4:

| word | successful deletion paths P | epsilon-pruned parses G |
|---|---:|---:|
| `aaaa` | 1 | 2 |
| `aabb` | 2 | 1 |

Both directions of `P=1 iff G=1` fail. The audit exhaustively compared
q=2 through n=10 and q=3 through n=8, finding no grammar-language mismatch.
The alternative finite counting convention is a modified parse rule and
must not be attributed to the paper. See `BIEDL_GRAMMAR_AUDIT.md`.

## Directed literature and decision

Biedl's grammar solves recognition and asks about an LR(k) grammar; it does
not establish parse/path-count correspondence. Burns–Purcell's binary
enumeration uses a binary indexing-string characterization; Kurz's
fixed-n winning count is polynomial in q of degree at most floor(n/2).
General rewriting confluence concerns common endpoints and does not
identify unique successful sequences when all successful sequences end
at the empty word. No immediately equivalent Same Game theorem was found
in this **directed**, incomplete priority audit; absence is weak evidence.
Sources: https://arxiv.org/pdf/cs/0107031 ;
https://www.fq.math.ca/Papers1/45-3/burns.pdf ;
https://oeis.org/A035617/a035617.pdf ;
https://oeis.org/A035615 ; https://oeis.org/A035617 .
The full Burns–Purcell proof and later literature remain to be audited
before making a priority claim.

**Decision B, provisional:** the theorem has some structural relevance,
but a major new idea is required for enumeration. The branching complement
dominates observed winners and grows in the tested canonical census;
Biedl parse ambiguity diverges from deletion-path ambiguity. The high
frequency of exact two-move commutation suggests a possible trace quotient
with adjacent bridge critical pairs, which remains an untested counting
representation. A canonical decomposition or multiplicity correction
would be required. If the trace quotient fails to compress B, this
decision should revert to C. No generating function was fitted or formalized.

## Reproduction and limits

```sh
python recovered/lc004_same_game.py --root artifacts/control --qmax 4 --nmax 10
python public-lc004/scripts/exhaustive_verify.py
python research_cycle/census.py --ranges 2:15,3:13,4:11
python research_cycle/summarize.py
python research_cycle/pair_interactions.py --ranges 3:10,3:11,3:12,3:13,4:10,4:11
python semantics_audit/check_correspondence.py
python biedl_grammar_audit.py
```

No random seeds are used. The original verifier checkout is not modified.
This campaign's main census is exact over the stated finite universe, not a
proof of asymptotic behavior or the q≥3 enumeration formula. The plot uses
a log y-axis for observed canonical B-state counts only.

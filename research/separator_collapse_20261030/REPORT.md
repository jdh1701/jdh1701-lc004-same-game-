# Sparse rescue of separator budget skips and independent collapse census

Research date: 29 October 2026, America/New_York. Objective: the unresolved general Same Game winning-word enumeration problem, including A035617.

## Reconciliation and scope

The active base is PR38, branch research/ten-attacks-20261030 at c6f719c08d519e0656ce6b035c69bbe143d74e46. Its checked mathematical source is f919410e300e724914913e862f551967c989a5f6, hosted run40998017137 SUCCESS; subsequent changes are evidence only. Earlier PR37 source ba744372317983ce26c94e32d7f7cd176c4893ac is also green at run40994461526.

This branch preserves both development histories with a merge commit and reuses LC004/SeparatorDeletionLink.lean from PR38. The earlier standalone CollapseCriterion.lean attempts failed elaboration at point_sum (runs40999056173 and40999863015) and are retired as redundant, not counted as proofs. Their source remains in commit history and failure excerpts remain here. No existing Lean theorem is modified.

PR38 already includes overlapping profile experiments and richer topology obstructions. This report does not add the two census totals together or claim their intersection as new progress. Exhaustive (4,6), (4,7), (4,8), and (6,8) coverage extends that reported campaign; other overlapping profiles primarily provide independent reconstruction and trace replay. Worldwide novelty is unassessed.

## Resolution of all 32 source-pipeline budget skips

PR38 deep_holdout.json recorded 32 inputs skipped because their original generator families exceeded 400 (maximum 3,591). The exact inputs were recovered from evidence.tar.gz at the immutable base commit, Git blob 3c87429e67a431f008dfbf2b003d6e893be43c70, and retained in skipped-inputs.json.

All 32 now evaluate without skips. Twenty-six have coefficient zero: nine collapse using certified dominated vertices, and seventeen require elementary free-face collapses after domination. All collapse steps are replayed against their defining conditions. The six survivors have coefficients 8, 10, and -4, twice each. This resolves that source pipeline's budget frontier; some coefficients may already have occurred in other targeted prior experiments.

The method keeps facets sparse. Every facet normalization has an explicit coverage check; every retained facet was an input and every input is contained in a retained facet. Domination removes v only when every maximal facet containing v also contains a distinct w. A separate replay checks every such condition. The reduced core uses exact deletion/link recursion with explicit state/time bounds. Residual faces are expanded only below 300,000 estimated faces, with a checked inverse vertex relabeling. All 32 decision values agree with direct alternating face sums of their reduced cores. Every complete original generator family is compared with the separate global interval-recursion generator, and full generator join is checked anew.

The deterministic compressed receipt contains complete strong and elementary traces, original-facet hashes, residual facets and vertex maps. Reproduction compares all untimed result fields against the committed receipt. These are computational certificates (VERIFIED-COMP), not individual Lean proof terms.

## Mathematical object

For a fixed color pattern p, take all original noncrossing pair/triple certificate partitions refining p. For each original color class, use every nontrivial unordered two-part cut of that class as a separator vertex. A certificate facet contains precisely the cuts that it refines. The complex K(p) is the union of the simplices on these facets, with the empty face included whenever at least one certificate exists.

The previously proved original-game identity gives

    winningJoinCoefficient(p) = sum_{S in K(p)} (-1)^|S|.

This is minus the reduced Euler characteristic for a nonvoid complex. It counts a signed coefficient of a fixed pattern, not winning words or deletion histories. These coefficients feed the existing exact counting polynomial; evaluating and enumerating them uniformly remains unresolved.

A common proper refinement of every generator already forces coefficient zero. We focus on the harder cases where the join of all generators is p. Generator completeness is compared for EVERY crossing input between two algorithms: classwise local NC catalogues with cross-class crossing tests, and an independent global first-block interval recursion on the actual word.

## Exhaustive finite result

Ten class-size profiles were checked: (4,6), (4,7), (4,8), (5,6), (5,7), (5,8), (6,6), (6,7), (6,8), and (7,7). Equal-size profiles retain only the class containing position zero, removing the color-swap duplication. Unequal-size profiles distinguish the smaller class, which also represents each unlabeled equality pattern once.

There are 10,473 distinct two-class patterns, of which 10,364 are crossing. Exactly 1,156 crossing cases have zero coefficient despite a full generator join. EVERY one collapses to a point by elementary free-face collapses. Every collapse step was independently replayed using global coface incidence, rather than trusting the codimension-one data structure used to find it. Per-pattern trace hashes and full first-example traces are retained in census.json.gz.

| Sizes | Crossing patterns | Full-join zeros | Independently replayed collapses |
|---|---:|---:|---:|
| 4,6 | 200 | 15 | 15 |
| 4,7 | 319 | 22 | 22 |
| 4,8 | 483 | 30 | 30 |
| 5,6 | 451 | 44 | 44 |
| 5,7 | 780 | 72 | 72 |
| 5,8 | 1274 | 117 | 117 |
| 6,6 | 456 | 53 | 53 |
| 6,7 | 1703 | 208 | 208 |
| 6,8 | 2989 | 364 | 364 |
| 7,7 | 1709 | 231 | 231 |

This supports a uniform collapse mechanism for zero coefficients. It does NOT prove it for untested profiles or three or more classes. A stalled greedy collapse would be recorded as inconclusive unless a homology obstruction were found; no stalled case occurred in this census.

## A higher-dimensional survivor

The (7,7) pattern 00001001101111 has twenty original certificate generators and coefficient -4. Its separator complex has reduced Betti vector beta_2=4, all other reduced Betti numbers zero, over F_2. This is an explicit higher-dimensional survivor, rather than a zero case.

Independent checks agree:

1. Alternating face sum of the complete separator complex.
2. Signed joins of actual local partition refinements, which preserve the original joins classwise.
3. Partition-lattice Mobius inversion of an independent raw maximal-run solver over every no-singleton refinement (26,244 for this witness).
4. Matching mod-two homology of the original separator complex and its independently constructed facet-incidence nerve.

Nonzero second homology excludes a homotopy equivalence with a one-dimensional graph. It does not exclude graph-based encodings with higher-dimensional reconstruction, or a compact scalar counting identity. Homology alone does not establish a wedge-of-spheres homotopy type.

Examples with coefficients +2 and +6 have corresponding first homology in the selected witnesses. No general classification of all survivor homology types is asserted. As another warning against overinterpreting Euler characteristic, the single six-point local complex has reduced beta_0=3 and beta_1=2, despite its coefficient being only -1.

## Verification boundaries

The complete finite census is VERIFIED-COMP. All classwise generator sets agree with the global recursion. Signed-join evaluation is exhaustive for total size at most twelve; larger profiles use a bounded set of independent join checks including every newly encountered coefficient value. Every selected nonzero witness is independently checked by raw-game Mobius inversion, and original/nerve homology agrees. A circle plus an isolated point is a negative control: its Euler sum is zero but its reduced homology is nonzero, so the program must not declare it collapsible. A cone is a positive collapse/replay control. Boundary spheres in dimensions zero through four give the expected homology.

Both homology calculations use the same exact GF2 elimination routine on independently constructed boundary complexes. They are not two independent implementations of linear algebra. The separate raw-game calculation supplies an independent coefficient check, not a separate proof of every Betti number. No floating point, fitted sequence, or learned classifier is used.

The reusable formal criterion is already proved in PR38: LC004.winningJoinCoefficient_zero_of_elementary_trace derives vanishing of the original coefficient from a verified trace on the actual complete indexed separator complex. LC004.facetAlternatingSum_deletion_link and LC004.facetFaces_eq_of_mutual_cover justify the sparse operations at the mathematical level. UseExistingCollapse.lean audits five reused declarations and their transitive axiom dependencies, permitting only propext, Classical.choice, and Quot.sound. It introduces no new theorem. The individual Python traces are not imported into Lean in this work.

The earlier exhaustive exact job passed hosted run40999056173. The new merged-source workflow rebuilds the existing formal foundation and audit and reruns the entire census, independent checks, and 32-case rescue. The merged-source run41002449977 PASSED both jobs at exact source81bca891be8f9f7534444a3fb3cbc9073171af4a. CI_RECEIPT.json and the lean-verified.log/exact-verified.log excerpts record this completed verification. Subsequent checkpoint edits affect evidence and documentation only.

## Strongest surviving research target

For winning crossing-connected patterns with at least two classes, every class of size at least five, and whose original certificate generators have full join, investigate whether zero coefficient forces an elementary collapse of the actual separator complex to a point. The converse follows from the existing formal criterion when its actual-complex assumptions are supplied. The winning/nonvoid qualification matters: a losing word has an empty generator family and a void complex, so Euler zero alone cannot imply a collapse to a point.

A proof must construct a uniform free-pair rule from the geometry. Checking every case of another fixed profile is not a substitute. The next step is to inspect the retained collapse traces for such a rule, then test it on a new three-class or larger-class family. Separately, the surviving nonzero patterns still need an enumeration law. Even a complete zero classification would not by itself solve A035617.

## Reproduction

    python3 research/separator_collapse_20261030/probe.py --profiles '4,6;4,7;4,8;5,6;5,7;5,8;6,6;6,7;6,8;7,7' --output research/separator_collapse_20261030/census.json
    python3 research/separator_collapse_20261030/independent.py
    python3 research/separator_collapse_20261030/rescue_skips.py
    lake build LC004.SeparatorDeletionLink
    lake env lean research/separator_collapse_20261030/UseExistingCollapse.lean

The committed archive is deterministic gzip JSON with timing fields removed. Full traces for representative zeros and hashes for all zero-case traces are included. Recompute traces with the source to verify every hash. Standard-library Python suffices. No local Sage or Lean pass is claimed in this continuation, and no worldwide novelty claim is made.

## Research queue and remaining obstruction

1. Extract a geometry-dependent free-pair rule from the retained traces, including the cases where domination stalls. Reject rules on explicit counterexamples before formalization.
2. Test candidate rules on crossing-connected three-class inputs, with explicit budgets and independent original-generator checks.
3. If a uniform rule survives, prove existence of its trace in Lean; the generic trace-to-zero theorem is already available.
4. Classify and enumerate the nonzero coefficient families, then sum their contributions in the exact counting polynomial.

There is no justified percentage solved or fixed count of mathematical steps remaining. The new result is a finite, reproducible elimination of all 32 recorded budget skips, not a general recurrence for A035617.

Reproducibility correction: the first archive comparison compared an in-memory tuple pattern with its JSON list representation. It rejected equal serialized data. The comparison now canonicalizes tuples and lists identically; arithmetic and trace replay were unaffected. This failure is retained in the CI history rather than silently treated as a pass.

## Post-domination strategy obstruction (local exact computation)

Among the 17 rescued zeros requiring elementary collapses after the recorded domination sequence, 14 resulting cores have minimum free-face dimension 2 and three have minimum dimension 3. In particular, none of these cores has a free vertex or edge. The three stronger examples are 000011111000001111 (1,820 generators), 001100000001111111 and 001111111000000011 (3,591 generators each), all of profile (9,9). A rule restricted to deleting free vertices, edges, or triangles cannot even start on these three specific cores.

This claim concerns the recorded residual complexes. It does not assert that every domination order gives the same core, that these are globally minimal counterexamples, or that no different higher-level decomposition exists. All three cores do collapse by the retained higher-dimensional traces. Their full complexes have 18,972, 54,528 and 54,528 faces, respectively. An independent global coface-intersection check examined all 1,737, 3,231 and 3,231 nonempty faces of dimension at most two and found none free. A free tetrahedron/four-simplex pair is supplied in core-obstructions.json for each, proving the stated minimum is attained.

The following standalone diagnostic reproduces the low-face obstruction from the immutable receipt. It imports no collapse-search helper. This diagnostic is VERIFIED-COMP locally; it is not a new Lean theorem or part of the hosted source audit.

```python
import gzip, json
from pathlib import Path
rows = json.loads(gzip.decompress(Path("rescued-results.json.gz").read_bytes()))["rows"]
for r in rows:
    if not r["elementary_trace"]:
        continue
    fs = r["strong_core_facets"]
    free = []
    for t in fs:
        bits = t
        while bits:
            v = bits & -bits
            bits -= v
            s = t ^ v
            if s and all(s & f != s for f in fs if f != t):
                free.append(s)
    minimum = min(s.bit_count() - 1 for s in free)
    if minimum < 3:
        continue
    vertex_map = r["elementary_vertex_map"]
    compact = lambda f: sum(1 << i for i, v in enumerate(vertex_map) if f >> v & 1)
    F = {0}
    for f in map(compact, fs):
        s = f
        while s:
            F.add(s)
            s = (s - 1) & f
    low = [s for s in F if s and s.bit_count() <= 3]
    # Independent incidence intersection gives ALL cofaces, not only facets.
    incidence = {1 << i: {f for f in F if f >> i & 1} for i in range(len(vertex_map))}
    for s in low:
        cofaces = set.intersection(*(incidence[1 << i] for i in range(len(vertex_map)) if s >> i & 1))
        assert len(cofaces) != 2
    print("".join(map(str, r["pattern"])), minimum, len(F), len(low))
```

Final verification checkpoint: [hosted run41002449977](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41002449977) is SUCCESS at source81bca891be8f9f7534444a3fb3cbc9073171af4a. The exact job reproduces all ten census rows and all32 rescued inputs with no errors. The five audited Lean declarations are reused proofs, while the per-pattern traces and core-obstruction diagnostic remain computational certificates.

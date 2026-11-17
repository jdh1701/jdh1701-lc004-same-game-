# Ten further finishing attempts: connected support and the remaining obstruction

2026-10-30. **A035617 is not solved.** This continuation proves a general support
theorem and an exact interpolation consequence. It also executes ten distinct
finishing attempts, including direct counterexample searches. The counts below
are finite evidence with their stated scope, not ten claimed proofs of the
open problem. No percentage-to-solution or worldwide novelty claim is made.

## Reconciled starting point

The previous checkout was unavailable, so the active repository was cloned
again and checked against the actual branch history. The base is PR40 evidence
head `c685723815658cf6a3f195cef09450168f58dfeb`.

- PR40 final proof source `c1a61f49e9ee95fad21b8d422ddd3df981b54132` is now green:
  run **41004479610**, exact job **123896139335**, Lean job **123896139851**.
  Its class-cut, five-row and free-interval results can be promoted to PROVED-LEAN.
- Claude's subsequent PR41 source `d8cb27ed645fabf3fa78dab6fb8a2cd94b6d39bb` is
  green in run **41023074939**, including Lean job **123954714267**.
  `JoinRigidBlocks.lean` and `CrossedClassMinSize.lean` are reused byte-for-byte,
  with credit. They supply the crossed-class bound under certificate-join
  hypotheses. The new work discharges those hypotheses for the original
  coefficient and supplies the noncrossing-connectivity bridge.
- PR39's 32 resolved budget skips and 17 hard collapse cores are prior results.
  They are inputs here, not new discoveries or additional census cases.
- A final recheck found PR35 documentation commit
  `da553f659a2238dd30e9f65da5de324444f06f63`. It explicitly identifies
  NCConnected implying every class is crossed as the missing boundary bridge.
  `ConnectedClassCrossing.lean` closes that exact gap. This subsequent commit
  changes no proof source and contributes no additional numerical result.

## The new general theorem

Let kappa(p) be the original signed certificate-join coefficient, j the number
of original classes, and NCConnected mean that the noncrossing closure is top.
For every size and every mixed profile:

> If p is NCConnected, j >= 2, and kappa(p) is nonzero, then every class has
> at least five positions. Consequently n >= 5j. At n = 5j, every class has
> exactly five positions.

The proof has three substantive bridges. First, an uncrossed class gives a
proper saturated interval: either its closed minimum/maximum interval or the
open gap around a point outside the class. That interval defines a proper
noncrossing coarsening, contradicting NCConnected. Second, nonzero original
coefficient forces the original certificate family to have least upper bound p.
Third, Claude's size-at-least-four bound combines with the existing crossed-four
cancellation theorem to give size at least five. Summing class cardinalities
gives the threshold; equality forces every summand to attain its minimum.

For the actual connected polynomial

    K_n(b) = sum over NCConnected p of kappa(p) b^(number of classes),

Lean proves evaluation equals the existing `connectedGameWeight b n`, which is
already used by the original-game moment expansion. It is not a new postulated
sequence. The degree is at most max(1, floor(n/5)). For n > 0 its constant term
is zero. Thus for 0 < n < 15:

    2 K_n(b) = 2b(2-b) K_n(1) + b(b-1) K_n(2),
    K_n(3) = 3 K_n(2) - 3 K_n(1).

For 0 < n < 20 Lean also proves the exact correction:

    K_n(3) = 3 K_n(2) - 3 K_n(1) + 6 [b^3] K_n(b).

The cubic coefficient remains a genuine counting obligation. The identity
does not solve it. The all-five boundary law supplies structure at n=5j, but
its survivor counts for arbitrary j and all positive-excess mixed strata
still need an effective enumeration.

New modules: `ConnectedClassCrossing`, `ConnectedCoefficientSupport`, and
`ConnectedCoefficientInterpolation`. Final local verification covers **241
active modules and 4,065 project declarations**, standard axioms only. Source
and negative guards pass. Hosted status and the exact source pin are recorded
separately in `../connected_support_20261030/receipts.json`.

## Ten routes actually executed

| # | Proposed finishing route | Executed result | Consequence |
|---|---|---|---|
| 1 | Eliminate all subcritical profiles and enumerate by excess n-5j | General Lean support, equality-profile and degree theorems; 5,296 geometry checks through n8, exact original joins through n11, and 27 independent raw-game Möbius checks | Real structural progress. Positive excess still has no general counting rule. |
| 2 | Recover three-color enumeration from the solved binary problem | Lean interpolation theorem; exact formal-series inversion reconstructs known W0..W14. The known all-five cubic coefficient -35 extends to n15 | Positive reduction, not new sequence terms. At n16 the cubic coefficient is -312, extracted from known ternary data. The polynomial b(b-1)(b-2) vanishes at 0,1,2 and changes b=3, proving that binary values and the degree bound alone are insufficient. |
| 3 | Use matroid bases and a Tutte-type enumeration of minimal top joins | After 45 tested eligible patterns, one seven-generator family has minimal top-joining subsets of sizes 2 and 3; all eight bases independently replayed | KILLED: these minimal families are not always matroid bases. |
| 4 | Replace separator complexes by graphs using the flag-complex property | After 67 full-join patterns, a triangle is absent although all three edges are present; complete facets independently regenerated | KILLED: the one-skeleton does not determine the complex. |
| 5 | Delete five-classes recursively using a closed smaller-pattern grammar | Projection can differ from the unrestricted remaining pattern. Exact conditioned barrier rows checked in 1,231 patterns / 6,155 fibers | Naive closure KILLED. Barrier-conditioned recursion remains exact but has no proved finite or tractable state family. |
| 6 | Determine the coefficient from the compatibility Gram spectrum | Initially survived 2,458 cases; expanded search finds a collision at checked case 4,039, profile (6,8). Exact determinants independently replayed | KILLED. The two coefficients are 0 and -1 although both characteristic polynomials are t^6(t-1)(t-4). |
| 7 | Characterize all-five survivors by hereditary class-deletion obstructions | The first certified n25 survivor loses support after restricting to two still-crossing classes: original coefficient -1, restricted coefficient 0 | KILLED for this hereditary support formulation. |
| 8 | Decompose a separated certificate pair into noncrossing SCC species | All 165 separated pairs in crossing (5,5) patterns checked. Five nontrivial SCC restrictions are intrinsic survivors; other SCC blocks cross | Direct noncrossing species decomposition KILLED. Intrinsic-component evidence is retained without claiming independent assembly. |
| 9 | Import formulas for meanders with one shallow side through interval certificates | A certified all-five survivor has exactly two certificates, and neither is an interval partition | The direct applicability hypothesis fails. An unknown transformation to shallow meanders is not ruled out. |
| 10 | Compress successful hard collapses into large Boolean intervals to obtain a uniform cancellation description | Replayed all 17 old hard cores, 88,105 elementary pairs, with exact live-coface checks. Maximal contiguous-prefix interval compression achieves zero reduction | This compression strategy makes no gain. The old collapses remain valid; no uniform collapse or enumeration theorem follows. |

Route 6's explicit words are `00010011101001` (coefficient 0) and
`01011000101100` (coefficient -1). Both have class profile (6,8) and five
compatible local-certificate pairs. The independent replayer checks all signed
subsets of the original certificates, and checks the two degree-eight
characteristic polynomials at nine integer arguments each using exact rational
Gaussian elimination. Thus this failure is not a floating-point collision or
an assumption about the Euler bridge.

Route 7's survivor is `0011022001331124422344334`; keeping its first two classes
gives `0011000111`, which has nine certificates and coefficient zero. Full
certificate enumeration and original signed joins verify both values.

The interpolation ambiguity in route 2 is an information obstruction under
the specified inputs, not a construction of two different Same Game models.
The bounded searches and route 10's failure do not disprove every stronger
matroid-like, decorated, grammar, or collapse approach.

## Literature gate

Sources checked on 2026-10-30:

- [OEIS A035617](https://oeis.org/A035617) supplies the 26 known ternary terms.
  Its old comment still describes b>=3 enumeration as apparently unsolved;
  this is not an exhaustive current-literature certification.
- [OEIS A035615](https://oeis.org/A035615) records the binary formula
  W_n(2)=2^n-2n F_(n-2)-(-1)^n-1 for n>=2, attributed to Burns and Purcell,
  *Counting the number of winning binary strings in the 1-dimensional same
  game*, Fibonacci Quarterly 45(3), 2007, pp.233-238. This is prior work.
- Fukuda and Nechita, [Enumerating meandric systems with large number of loops](https://arxiv.org/abs/1609.02756),
  Ann. Inst. H. Poincaré D 6(4), 2019, pp.607-640, DOI 10.4171/AIHPD/80:
  a possible fixed-defect analogy. No weight-preserving correspondence to
  our connected coefficients has been established.
- Fukuda and Nechita, [Generating series and matrix models for meandric systems with one shallow side](https://arxiv.org/abs/2103.03615),
  Ann. Inst. H. Poincaré D 11(2), 2024, pp.299-330, DOI 10.4171/AIHPD/183:
  interval partitions are the pertinent restrictive hypothesis. Route 9 checks
  that hypothesis explicitly instead of importing the formulas automatically.

## Reproduction, failed attempts, and next mathematical target

From the repository root:

```sh
python research/fiber_elimination_20261030/restore_baseline.py
python research/connected_support_20261030/check_support.py
python research/finishing_routes_20261030/routes.py
python research/finishing_routes_20261030/spectral_stress.py
python research/finishing_routes_20261030/replay.py
python research/finishing_routes_20261030/interval_compression.py
lake build LC004
lake env lean scripts/AxiomAudit.lean
python scripts/check_lean_coverage.py
python scripts/test_verification_guards.py
```

Machine-readable witnesses, full traces, build/audit logs, and unsuccessful
Lean attempts are preserved in `evidence.tar.gz` with a SHA-256 manifest.
The first interval replay failed because an old trace used compressed vertex
indices; the corrected replayer explicitly applies the stored vertex map.
Both the failure and corrected replay are retained. No old compiled root is
used as evidence for the final interpolation module.

The next focused target is a tractable enumeration of the first positive-excess
layer, beginning with profile (5,5,6), together with the arbitrary-j all-five
survivor sequence. The support theorem now proves why these are the relevant
unknown contributions. A successful rule must retain local separator incidence:
the spectrum and class-deletion counterexamples show that discarding it loses
the actual coefficient. Even a complete first-excess result would be a partial
resolution, not a solution for all lengths and all excesses.


## Final hosted verification

**PROVED-LEAN** on exact source `f653c28b15697dd6b9a4b53771fe46beeeb83986`,
[run 41029475200](https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/41029475200).
Lean job **123975457884** and exact job **123975457523** both passed. The hosted
logs confirm 241 active modules, 4,065 audited declarations, standard axioms
only, and passing negative guards. The independent original-certificate
replay and all ten route scripts also pass on this exact source. This receipt
supersedes the earlier pending status; no proof source changed after the run.

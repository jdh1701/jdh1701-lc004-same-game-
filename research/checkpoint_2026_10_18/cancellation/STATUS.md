# Four-position cancellation checkpoint

Date: 2026-10-18. Base commit: `f2eef1f724258de2e6a08ffd83dfeb77f9fa5ab2`.

Subsequent update: the [four-gap witness checkpoint](../gaps/STATUS.md)
discharges intersection invariance for the complete specified regional
witness families and their actual board-position geometry. This report
retains the status at the earlier base; full-board transport remains open.

The general enumeration problem remains unresolved. The fixed roadmap still
has **9 major stages: 4 verified, 1 partial, 4 open**. This checkpoint does
not close another stage or claim an end-to-end small-block theorem in Lean.

## New formal results

Twelve named theorems, including helpers, were added in four modules:

- `CoefficientBarrier.lean`: a general theorem forcing coefficients outside
  a meet barrier to vanish; the four-gap grammar intersection identity; and
  the two-indicator inclusion-exclusion identity.
- `UnionCoefficientIdentity.lean`: coefficient-level union/intersection
  identities, fixed-coordinate support, and cancellation at the joined key
  of two branches under an explicit intersection-invariance hypothesis.
- `FourBlockCancellation.lean`: the two actual noncrossing pairings of four
  positions join to the full block; their conditional cancellation theorem
  applies the preceding machinery to these concrete setoids.
- `ChordBarrier.lean`: a noncrossing block disjoint from chord endpoints cannot
  connect the strict interior of that chord to its exterior.

The general four-block theorem retains the hypothesis `hinv`: intersection
coverage must be unchanged by imposing the gap partition. This remains a
geometric application obligation. It is not silently replaced with an axiom.
See [ARGUMENT.md](ARGUMENT.md) for the full proposed combinatorial proof and
the precise formalization boundary.

## Executed discrimination tests

`test_small_blocks.py` checks all equality patterns through n=10 with a
selected block containing position zero of size two, three, or four. It tests
the exact gap-product coefficient formula, including zeros and singleton
blocks elsewhere, using the full signed witness map.

| Check | Number | Result |
|---|---:|---|
| Size-two coefficient formula | 46,113 | All pass |
| Size-three coefficient formula | 38,639 | All pass |
| Size-four coefficient formula | 20,614 | All pass |
| Crossing cases among those coefficient checks | 79,990 | All coefficients zero |
| Forced four-position pairing/gap equivalences | 20,614 | All pass |
| Rotation invariance on nonzero support | 9,285 | All pass |

The coefficient checks total **105,366**. The crossing checks are a subset,
not additional independent observations. The pairing checks compare explicit
refining witnesses with the separate grammar recognizer. The coefficient tests
share the existing witness generator and signed-join engine; they are not
independent raw-game evidence or Lean certificates.

The stronger extension to size five was falsified at length ten:

```text
partition: 0010011011
actual signed coefficient: -1
small-block gap rule would predict: 0
```

This demonstrates why the cutoff matters. Conversely, an isolated four-cell
block has coefficient -1, so the rule must not be misstated as eliminating
every four-position block.

## Verification and next work

The pinned Lean 4.19.0 targeted builds passed. The final axiom report and
source audit are stored alongside literal successful and failed development
logs. No proof holes or custom axioms were introduced. The four-gap grammar
identity uses no axioms; other reports contain only standard Lean axioms or
subsets. The root imports the new modules, and CI runs the whole project.

```sh
lake build
lake env lean research/checkpoint_2026_10_18/cancellation/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/cancellation/test_small_blocks.py
python3 research/checkpoint_2026_10_18/cancellation/audit.py
```

Next: discharge the forced-pairing/gap equivalence and coefficient transport
in Lean, then assemble the minimum-five support theorem. Even that theorem
would leave the connected coefficient sequence and general enumeration
recurrence unresolved. No originality assessment is claimed here.

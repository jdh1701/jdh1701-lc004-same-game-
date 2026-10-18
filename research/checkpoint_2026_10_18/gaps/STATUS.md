# Four-gap witness construction checkpoint

Date: 2026-10-18. Base commit: `1018891a8e7aa450af1fb8549ee5fc8eeffdd8a5`.

The general winning-word enumeration problem remains unresolved. The fixed
roadmap still has **9 major stages: 4 verified, 1 partial, 4 open**. Five stages
need further work; they have unequal difficulty. This checkpoint adds **24
named Lean theorems, including helpers**, without closing another whole stage.

## What is now proved

The previous coefficient theorem assumed that intersection coverage was
unchanged by imposing the four-gap partition. This checkpoint proves that
invariance for the two specified regional pair/triple witness families, by
constructing a new witness from any two witnesses in their intersection.

For four positions a < b < c < d, number the cyclic gaps 0, 1, 2, 3.
The final gap includes both the prefix before a and the suffix after d.

| Family | Isolated gaps | Gaps allowed to share blocks |
|---|---|---|
| Adjacent pairing (a,b), (c,d) | 0 and 2 | 1 and 3 |
| Nested pairing (a,d), (b,c) | 1 and 3 | 0 and 2 |
| Their intersection coverage | All four | None |

Given a witness from each family, keep the first witness's blocks in gaps
0 and 2 and the second witness's blocks in gaps 1 and 3. Lean proves that
this operation preserves entire blocks, their sizes, noncrossing, and the
ambient equality constraints. Conversely, a witness confined to all four
gaps belongs to both regional families. This proves the coverage identity
for arbitrary finite ordered carriers satisfying the stated gap geometry.

The coefficient machinery then proves zero at a remainder partition that
connects distinct gaps, when the four-position coordinate is the full block.
`positional_regional_four_block_zero` specializes this result to arbitrary
four ordered positions of a board. Its only explicit mathematical premises
are their order and the target remainder partition failing to refine the
gap partition. No intersection-invariance or list-completeness premise is
left in that theorem.

The family being counted is explicitly `regionalFourBlockFamily`: a union
of the adjacent and nested pairing coordinates with complete regional
witness lists. Those lists are **noncomputable finite specifications** of
all qualifying setoids. They are not the executable Python generator and
do not close stage C2 or E2.

## Formal files

| Module | Named theorems | Role |
|---|---:|---|
| `PairGapDecomposition.lean` | 5 | Forced pairs imply chord-region refinement; exact regional criterion for an existing partition |
| `WitnessGluing.lean` | 4 | Construct a partition by retaining whole blocks from two witnesses |
| `FourGapWitnesses.lean` | 5 | Prove intersection coverage, meet invariance, and cancellation for specified witness lists |
| `FourGapGeometry.lean` | 7 | Identify both chord-region partitions with actual cyclic gaps and prove their geometry |
| `RegionalCancellation.lean` | 3 | Complete specification lists and the positional regional cancellation theorem |

The forced-pair refinement statements apply to actual noncrossing partitions
with the indicated pair blocks. The restriction criteria recover global
validity of a given partition from its regions. They do not yet construct
the full-board partition from an arbitrary remainder and pairing coordinate.

## Exact remaining boundary

The theorem's coefficient is still a coefficient in the product of a
four-position partition lattice and the remainder partition lattice.
The following work is required before claiming the full-board small-block
theorem or the minimum-five connected-support conclusion:

1. Prove locality: witnesses not refining a target partition do not affect
   that target's coefficient.
2. Construct the full-board/product order isomorphism and transport the
   signed coefficients through it.
3. Prove that every qualifying witness refining an isolated four-position
   block uses exactly one of the two pairings; prove complete restriction
   and extension of witnesses across the endpoints and remainder.
4. Assemble the size-two, size-three, and size-four results and the crossing
   component consequence. Product factorization still needs its full assembly.
5. Identify the specification families with the executable first-block
   generator and finish the grammar-to-raw-game direction.

These are local obligations within the existing roadmap, not five newly
invented major stages. The four-gap geometry here handles arbitrary endpoint
positions directly, so it does not require a rotation theorem. Any rotation
transport used elsewhere remains a separate obligation.

Even the eventual minimum-five theorem would only bound the degree of the
connected coefficient polynomial. It would not determine all connected
coefficients or establish a useful general enumeration recurrence. Stage F
and the end-to-end theorem remain open. No novelty claim is made.

## Verification

The pinned Lean 4.19.0 targeted build accepted all five modules. The literal
axiom report lists all 24 named theorems; only standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`, or subsets, occur. The source
audit checks the whole LC004 source set for proof holes and custom axioms.
The root imports the new modules. CI runs the full root build, all existing
experimental checks, and a fresh axiom report for this checkpoint.

```sh
lake build
lake env lean research/checkpoint_2026_10_18/gaps/PrintAxioms.lean
python3 research/checkpoint_2026_10_18/gaps/audit.py
```

Successful and failed development logs are retained with their meanings in
`logs/README.md`. No new finite counts or raw-game experiments are claimed
in this checkpoint; the advance is a general kernel-checked construction.

# Four-gap Lean checkpoint — 29 October 2026

Base proof repository: jdh1701/jdh1701-lc004-same-game-, commit
d5861420ee776b9618c56c114a84e7c1c870b16d. This branch adds nine modules and
31 theorem declarations. The prior paper argument is preserved in
jdh1701/Alexandria_Omega_New at commit 31a286a1616a4a0bc8313d62190589545e361ffe,
research/LC004/2026-10-29-four-gap-cancellation/FOUR_GAP_CANCELLATION.md.

## Completed formal results

1. `certificate_four_class_block_length` and `certificate_four_class_card`:
   blocks inside a single four-occurrence color class must be pairs. There
   is no restriction on other colors, which may have arbitrary multiplicities.
2. `certificate_four_two_shapes`: those pairs have the separated or nested
   shape. External certificate blocks may include triples.
3. `winning_pair_interior` and `winning_pair_exterior`: a forced certificate
   pair gives winning restrictions on its interior and exterior. The exterior
   includes both ends of the linear word in one ordered region.
4. `winning_iff_two_pairing_witnesses`: for a four-occurrence class, winning is
   exactly the union of the two pairing-witness predicates.
5. `four_gap_overlap_iff`: the intersection of these predicates is exactly
   winning in all four gaps. Different external certificates are allowed.
   The reverse implication constructs witnesses by noncrossing region assembly.
6. `winning_splitOffPair_iff`: a pairing witness is equivalent to genuine
   winning for the corresponding split-color pattern.
7. `four_gap_winning_indicator`: the exact integer indicator identity used in
   the paper's cancellation proof, now stated on actual winning color patterns.
8. `collectedJoinCoefficient_incidence`, `winningJoinCoefficient_incidence`,
   `winningJoinCoefficient_unique`: collected signed coefficients are the
   unique lower-incidence expansion of the original game's winning indicator.
9. `incidence_support_of_meet_invariance` and its local version: if the lower
   transform only depends on meet with rho, coefficients outside its principal
   ideal vanish. The local version only assumes invariance below the target p.
10. `winning_iff_noncrossing_region_cover`: exact winning decomposition for a
    saturated disjoint noncrossing cover, supplying the geometric input to the
    noncrossing-component factorization proof.

## Exact central theorem

For a<b<c<d forming one complete color class of p, Lean proves

    [WinningColorPattern p]
      - [WinningColorPattern (splitOffPair p c d)]
      - [WinningColorPattern (splitOffPair p b c)]
        = -[FourGapsWin p a b c d],

where brackets are integer indicators. `splitOffPair` is defined as the meet
of p with the kernel of the Boolean membership function for the designated
pair. It creates the precise equality-pattern refinement; it does not change
the legal-move rule. `WinningColorPattern` is the existing certificate-based
predicate already linked to maximal-run erasure by
`winning_word_pattern_iff` and `winning_color_pattern_iff_raw_win`.

## Verification

Lean 4.19.0 and the unchanged pinned Mathlib manifest were used. The full
root build succeeds; all 171 active modules are in its import closure.
Source guards reject placeholders and unsafe proof bypasses. The project
axiom audit and negative guard results are stored in research/four_gap_verification/.
Every accepted new theorem printed only propext, Classical.choice, Quot.sound.
The final project-wide audit is the authoritative combined receipt.

This execution used the existing /tmp/lean-ownpath.so path-resolution shim
documented by earlier verification work. Its only override is readlink for
the executable path. Compiler, elaborator and kernel logic are unchanged.
Local command wrappers used absolute Lean/Lake paths for the same reason.
Neither is required in normal hosted CI. A dedicated branch workflow has
been added; local success must not be described as hosted CI success until
the hosted run itself completes and is inspected.

## Remaining formal and mathematical boundary

The universal crossed-size-four coefficient cancellation theorem is NOT yet
Lean-certified. Neither is the free-cumulant vanishing bound. The paper proofs
remain intact; this checkpoint certifies their principal geometric identity
and incidence-algebra prerequisites, not their complete assembly.

One shorter formal route is now available. For a target p with its four-class A,
work only on the refinement ideal below p. Subtract the two split indicators.
Their collected coefficient at p equals c(p), since p is not below either
split kernel. Prove that the resulting indicator is invariant under meet with
the partition consisting of A and the four gaps. The local incidence-support
theorem then gives c(p)=0 whenever another class spans gaps. This avoids
formalizing the entire product formula for the partition-lattice Moebius function.
It still requires a proved overlap identity for arbitrary refinements below p,
including refinements that split A; the current central theorem assumes A
is one class in its input. That assumption must not be silently dropped.

After that, formalize least noncrossing coarsening, the component bijection,
coefficient product factorization, and its identification with free cumulants.
Only then can the universal n<5j support bound be marked PROVED-LEAN.

The full fixed-alphabet OEIS A035617 enumeration remains mathematically open
in this development. The nonzero connected coefficients at and above the
support threshold still need an effective enumeration. No novelty, full-solution,
or completion-percentage claim is made.

## Reproduction

    lake exe cache get
    python scripts/check_lean_coverage.py
    lake build
    lake env lean scripts/AxiomAudit.lean
    python scripts/test_verification_guards.py

The root imports all nine added modules. There are no unchecked source drafts
in the active Lean tree.

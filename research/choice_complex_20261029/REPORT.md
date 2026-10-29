# Choice-complex proof and baseline reconciliation, 2026-10-29

The new result is the complete written proof in [PROOF.md](PROOF.md): for a
noncrossing-connected partition into j >= 2 five-classes, its coefficient is
-1 exactly when there are two certificate refinements whose join is the
partition, and zero otherwise. **PROVED-PAPER**, awaiting independent review;
the universal statement has not yet been assembled in Lean.

This settles the structural conjecture on paper, not the enumeration of the
surviving pairs or the full fixed-q >= 3 problem. In particular it supplies
no new n=25 count. Claude's job remains queued at the last check.

## Baseline used

| Item | Receipt / limitation |
|---|---|
| Existing original-game Lean expansion | PROVED-LEAN, `0fb784ad778b0efe5f46260a24690c9b524b0f19`, CI 40931129635 success |
| Claude independent rebuild | CI 40935572104 success, 185 modules / 2324 audited declarations |
| Claude source reviewed | `research/free-cumulants-20261029` at `56d867dd07e781fe1565e8ab3761bb1c647e3009`; no new commits at reconciliation |
| Current research parent | `fd64c4d1f6b000b7ac59fd7b95a4ee3ce51fffe7`; CI 40945905280 in progress at last check |
| Mathlib / Lean | Both pinned to v4.19.0; fresh baseline build passed; new module imported in root |
| Earlier Sage control run | CI 40895249874 success, Sage job 123522462820, Lean job 123522463522 |
| Fresh Sage checks | Local Sage unavailable; new pinned-image homology job committed, no fresh pass claimed before CI completes |
| OpenAlex | Two focused queries returned HTTP 429; exact errors in `openalex.json`; no novelty conclusion |
| Literature actually read | Zhang, Yap, Jaffar (AAAI 1999), https://cdn.aaai.org/AAAI/1999/AAAI99-026.pdf |
| Claude n=25 pair scan | CI 40942806037 queued at last check; no result accepted |

The relevant mathlib finite-sum/involution machinery was reused. A local search
found convex geometric simplicial-complex infrastructure but no direct ready-made
version of this finite choice-complex argument. We did not rebuild every module
in mathlib or claim an exhaustive literature search.

## Claims and scope

| Claim | Status | Evidence |
|---|---|---|
| All-five >=3-certificate cancellation | PROVED-PAPER | `PROOF.md`, Sections 1–5; no claim of complete Lean formalization |
| Abstract two-fan / size-two-matching collapse theorem | PROVED-PAPER | `PROOF.md`, Section 4; the matching-size and connectedness hypotheses are essential |
| Dominated-vertex cancellation and facet version | PROVED-PAPER, with local Lean verification | `LC004/ChoiceComplexCancellation.lean`; exact-head CI pending at initial upload |
| Two-fan majority closure and row-completion lemma | PROVED-PAPER, with local Lean verification | Same Lean module; kernel reports standard axioms only |
| Full 126-pair classification / 13 orbits | VERIFIED-COMP | `structure.py`, `pair_orbits.py`, all cases; table also explicit in proof |
| Constructive collapse for 38 geometric examples | VERIFIED-COMP | `eliminate.py`, `structural_certificates.json`, independent replay; these are a biased sample |
| Four-binary-variable exhaustive stress test | VERIFIED-COMP | 117649 presentations; 116208 connected; 3681 distinct relations; 2640 nontrivial relations, every paper construction replayed |
| Five-valued abstract stress test | VERIFIED-COMP | 6000 seeded presentations at j=3,4,5; 1911 nontrivial, all coefficient zero; not exhaustive |
| Explicit general fixed-q enumeration formula | CONJECTURE (open target) | No formula for the connected kernel or surviving all-five pairs supplied |

CI run IDs for the new artifacts are recorded in `CI_RECEIPTS.json` once GitHub
has created the run. A pending run is not PROVED-LEAN evidence. The local full
build, coverage, axiom audit, and guard logs are retained here. Attempts 1–3
failed at runtime discovery before proof elaboration; attempts 4–6 compile
the successive Lean versions. No mathematical Lean failure is hidden.

## Correction to the strength of the previous sample

Of the 2674 earlier connected patterns with at least three certificates, 2636
have a constant choice coordinate. Their zero coefficient follows immediately
from a cone, so they do not test the difficult nonfrozen case. Only 38 do.

| n | Constant-coordinate cases | Nonfrozen cases |
|---|---:|---:|
| 10 | 16 | 10 |
| 15 | 158 | 14 |
| 20 | 299 | 10 |
| 25 | 1054 | 4 |
| 30 | 1109 | 0 |

All 38 admit a greedy strong collapse and, separately, the explicit construction
from the paper proof. The latter checks all domination steps on the original
facets. The universal claim now rests on the written argument, not on inflating
these 38 examples into large-size exhaustive evidence.

## Efficient next work

1. Have Claude try to break Sections 3 and 4 of the proof, especially preservation
   of the binary description and connectedness after eliminating bijections.
2. Formalize the exact-projection classification, bijective elimination and
   sink-value argument; then connect the finite local table and alternating
   face sum to `winningJoinCoefficient`.
3. Once independently accepted, use the theorem to justify exhaustive
   two-certificate enumeration as an exact all-five computation, rather than
   merely a support lower bound. Independently audit its enumeration coverage.
4. Work on enumerating the surviving pairs, or extend to mixed profiles with
   explicitly new hypotheses. The existing mixed-profile pair-graph formula
   remains KILLED; this proof does not revive it.

No additional broad analogy campaign is needed for these steps. No main merge
or changes to Claude's running branch were made.

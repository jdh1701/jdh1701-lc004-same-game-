# Exact Same Game proof campaign — 29 October 2026

## Objective and success criterion
Resolve fixed-alphabet enumeration (A035617, and ideally arbitrary b), with an
explicit tractable coefficient formula/recurrence, proof for all lengths and
alphabets, independently checked implementations, and essential Lean theorems.
An existing exponential signed-join sum, certificate count, or finite fit alone
is not completion. Use maximal-run deletion and count words without multiplicity.

## Baseline pins (checked before execution)
- main: 10a2c94a30a3a2812e0f68aa550c8ee53b3b0778.
- Verified four-gap branch: a2212dc08ca633cb6925208a865493648c237b0a;
  PR32, hosted run 40890080150 success; 171 modules, 2124 audited declarations.
- Claude free-cumulant branch: 9038f6bd8740da6a5583fa0ef314fc06b0adb2ab;
  adds NEGATIVE_RESULTS and redundant_atom.py since prior ac6fe4c.
- Joint handoff/archive: f997d5d119a1294b3f18dabc240599f201c2fa74.
- Primary computational/paper checkpoint: 31a286a; Lean mirror: 417efba.
New proof branch starts from a2212dc, preserving all accepted sources.

## Execution order and gates

1. Reconcile claims/provenance once. Read new commits rather than rerun known
   tables. Preserve the distinction among geometric joins, signed coefficients,
   certificates, words and scalar cumulants. No novelty claim from an empty
   search. Record available tools and failed access explicitly.

2. Finish crossed-four cancellation in Lean. Extend the winning-indicator
   identity from a complete four-class to all refinements below the target.
   Use existing collected coefficient uniqueness and local meet-invariance.
   Prove gap partition invariance, then coefficient vanishing. Gate: theorem
   states winningJoinCoefficient directly, no assumed cancellation oracle;
   root build + all-module axiom audit + exact-head hosted CI.

3. Formalize NC closure and connected coefficient factorization. Consult Lehner
   (2001/2002), Theorem 4.1 proof, as prior art for regrouping by NC closure.
   Check signed weight multiplicativity under NC regions: our weight is not
   automatically a product of classical scalar cumulants over individual blocks.
   Prove our game-specific factorization before invoking the shared mechanism.
   Then derive the universal n<5j support bound. This is a reduction, not a count.

4. Independently check the j=6 break with bounded-deficit profile extraction.
   Targets A(16,5), A(18,6); inputs must not import the claimed answers. Use
   rational/integer arithmetic, memoized content counts, truncate to required
   deficit; compare controls and hold-out values. Keep dependence on the
   face-profile enumeration formula explicit until its counting bridge is proved.
   Independent computation and independent mathematical assumptions are distinct.

5. Attack the surviving connected kernel using competing representations.
   A: cyclic orbits + rigid insertion classes (test against known orbit receipts).
   B: generalized linked-diagram/heap recurrences; distinguish commuting histories
      from unique words, test aabb/aaaa and known noncanonical-scheme examples.
   C: continued fractions and lattice paths suggested by Touchard (1952),
      Stein (1978), Nijenhuis–Wilf (1979), Lehner's lattice-path work. Derive
      weights from the game; arbitrary fitted Jacobi parameters do not explain it.
   D: multivariate formal series and coefficient extraction, allowing rational
      diagonals rather than forcing polynomial fits. Separate exact identity,
      asymptotic and empirical interpolation.
   Each candidate first faces smallest counterexamples, low-length full-pattern
   comparison, binary control, unused-color symmetry, n=0/1, and merged boundaries.
   Discard routes on decisive counterexamples; retain qualified partial lemmas.

6. Integrate only compatible verified modules, publish a precise theorem ledger
   and reproducible manuscript. No main merge by historical ordering alone.
   A complete solution requires new control of the nonzero connected weights;
   proving the support bound alone will not settle A035617.

## Tools and division of work
- Lean/CI: universal statements, original-game bridge, complete import and axiom audit.
- Python: exact independent oracles, finite posets, sparse content extraction,
  source/query archiving. Never promote finite checks to universal proof.
- SageMath: independent poset/Moebius and formal-series controls if executable
  access succeeds; do not claim Sage execution from merely writing a script.
  No local sage or apt candidate was found at baseline. Test documented remote
  SageCell access with public mathematical code; if blocked, retain the failure
  and use Python while a CI Sage job supplies an independent run.
- OpenAlex: archive exact DOI/title lookups and targeted citation searches;
  follow relevant references back to primary full text. Not a numeric OEIS engine.
- Claude: repository handoff, not a claimed direct API conversation. Assign
  independent profile recomputation and adversarial paper/literature review;
  keep Lean cancellation owned by GPT to avoid overlapping edits. No claim
  Claude has executed anything until a response or pushed evidence is read.

## Research efficiency and receipts
Do not repeat n<=15 signed-support enumeration unless a new representation
requires it. Do not pursue a universal redundant-atom involution: existing
cone tests have failures even after NC component factoring. Record the 30
length-12 failures and Claude's exceptions in the handoff. Bound literature
work by a concrete proof obligation and archive actionable matches, not volume.
Every completed session saves sources, exact inputs, pass/fail logs, hashes,
current status and the next unresolved statement. No completion percentage.

# Continue here: seven-class deletion, not another small census

Base is PR50 at a67850cafbf958447f9d8f58104bc349f6ae0061. PR35 was rechecked
at c88cc0906591ad2b79cdeb168f04a77bf5950553; no newer source was missed.
LC004/A035617 remains OPEN. Read REPORT.md and receipts.json for scope.

New uniform paper results:

1. For ANY nontrivial NCConnected p and distinguished seven-class H,
   kappa(p)=1_(no universal H-certificate)*beta(P)
   minus sum kappa(p minus e) over actual cyclic adjacent H-pairs e whose
   remaining H five-set still crosses a full outside class. Outside class
   sizes are arbitrary. P uses FULL outside separators, not merely choices.
2. Thus a universal H-certificate removes the projected term completely.
   `fast_coefficient.py` implements polynomial evaluation for arbitrary
   all-five patterns and for the universal connected (7,5,...,5) stratum.
   It returns None outside the latter domain. It is not a full solver.
3. Tripling the singleton of a five-class with runs (1,2,2) multiplies the
   coefficient by -2, even with arbitrary other class sizes. Iterating on
   s classes of an all-five survivor gives (-1)^(s+1)*2^s. The image family
   has ((5j+2s)/(5j))*binom(j,s)*A_j rooted patterns; this is not an exhaustive
   mixed-profile census or an A035617 term.

New formal file `LC004/SmallRefinementGap.lean` concerns small blocks in a
one-class refinement: nonzero coefficient forces consecutive original
occurrences inside that block to be globally adjacent, including wraparound.
Do not label the entire recurrence, multiplier, or Python evaluator as
Lean-certified. They use paper gap/cyclic/order-restriction assembly, PR50
Euler reduction, and the general five-class no-three-run theorem.

Exact regression: 4961 connected cases; 3920 direct original replays;
34727 pair correction checks; 4556 fast all-five checks; 269 fast universal
seven checks; 96 one-step tripling fixtures, 72 two-step and 8 three-step;
24 direct original replays of the complete j=2 constructed family.
These groups overlap and must not be added as independent patterns.
There are 805 universal cases and 4156 no-universal cases.

A PR50 zero-witness signed-join assertion used a noncanonical target and
could pass vacuously. It is repaired; its true value is still zero. All six
color relabelings of PR50's NONZERO +1 witness now guard normalization.

Next useful targets:

* Prove/evaluate beta(P) in the u=0 branch. It is an exact ternary constraint
  complex for otherwise-five classes. PR50's +1 connected witness has all
  deletion terms zero, so the new recurrence alone cannot remove this term.
  Projected majority closure is false even when kappa is nonzero.
* Determine whether universal-seven nonzero cases are exactly singleton
  triplings, or find a counterexample. The recurrence evaluates them without
  needing this stronger assertion; exhaustiveness is NOT established here.
* Use the arbitrary-outside-size recurrence to remove universal seven-classes
  iteratively, factoring disconnected deletion targets. Mixed six-classes and
  no-universal sevens remain genuine residual cases.
* Formalize the uniform recurrence or the general no-three-run bridge before
  calling the multiplier PROVED-LEAN. Avoid disguising a bounded catalogue
  check as the unbounded original-pattern assembly.

No local Lean runtime. Require hosted exact-source full build, all-declaration
axiom audit, import coverage, source guard and both negative guards. Archive
logs and failed attempts. User authorizes continued proof work and draft PRs.

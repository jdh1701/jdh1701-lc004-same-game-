# Noncrossing coefficient decomposition checkpoint — 29 October 2026

Base: e6dbea580447aae5b8d87a4095a186dc26107bb0, PR33, green hosted run
40895249874 (crossed-four cancellation). No new Claude commits were observed
beyond 9038f6bd8740da6a5583fa0ef314fc06b0adb2ab during the baseline check.

## Main advance

`winningJoinCoefficient_noncrossing_product` proves, for p refining a
noncrossing partition pi,

    c_n(p) = product_{B in pi} c_|B|(p restricted to B).

`winningJoinCoefficient_closure_components` specializes this to the least
noncrossing coarsening of p. These are coefficients of the already verified
original-game winning indicator. They are not certificate counts or history
counts. This discharges the weight-multiplicativity obligation identified in
the Lehner applicability audit; it does not by itself enumerate the connected
weights or prove the full cumulant support theorem.

## Other formal results

- Intrinsic least noncrossing coarsening, with extensivity, noncrossing,
  minimality, monotonicity, idempotence and the fixed-point characterization.
- NCConnected means that this closure is the single-block partition; a precise
  equivalent characterization forbids proper noncrossing coarsenings.
- An order equivalence between refinements of a partition and the product
  of the partition spaces on its blocks. This is an equality-pattern bijection.
- Winning equivalence across the actual blocks of every NC coarsening.
- Exact regrouping of arbitrary signed weights by closure fibers. It preserves
  lower incidence sums on noncrossing targets, without assuming multiplicativity.
- Generic product-incidence and restricted-ideal lemmas, used to derive the
  game-specific coefficient product from winning-indicator factorization.

The coefficient-product proof uses uniqueness of the finite incidence expansion
and the verified region order equivalence; it does not assume the desired
product formula as a hypothesis.

## Verification boundaries

Targeted local Lean 4.19.0 builds accepted all new modules. Standard axioms only
were printed for the final theorems. Full-root and exact-commit hosted receipts
are recorded separately when complete; do not infer their success from this
text or a commit message.

`check_components.py` independently enumerates every set partition through
n=7 and every refinement of each noncrossing partition. It checks leastness,
idempotence, regional winning factorization, incidence regrouping for a
nonmultiplicative signed control weight, and game-coefficient product identities.
The receipt includes 11,147 regional cases, exact integer arithmetic. This is
finite verification, not the universal proof. Empty-set conventions remain in
the Lean theorems, whose statements have no positive-length assumption.

A restored runtime required the previously documented executable-path shim;
archive extraction also required --no-same-owner in this host. Neither changes
kernel logic or pinned dependency sources. Normal hosted CI requires neither.
Initial elaboration failures in the product proof were traced to mismatched
DecidableEq choices in dependent Fintype products; an explicit DecidableEq
parameter in the generic product lemma resolves that instance mismatch. Failed
logs are preserved. No proof placeholder remains in the active sources.

## Next exact obligations

1. Show that restricting p to each block of nc(p) gives an NC-connected local
   partition, and prove the converse assembly statement. Then construct the
   precise closure-fiber/product bijection.
2. Account for the color-class exponent when weighting c(p) by b^number_of_classes.
   Obtain the multiplicative weighted fiber sums and identify them with the
   triangular free moment/cumulant recurrence, including n=0 separately.
3. Connect nonzero collected coefficients to certificate joins to import the
   existing size-two/three rigidity theorem, then combine it with crossed-four
   cancellation. Prove the n<5j support bound on the identified cumulants.
4. Enumerate the surviving connected coefficients. The support bound and
   factorization alone do not solve fixed-alphabet A035617.

Classical NC closure/regrouping has prior literature (Lehner 2001/2002).
No novelty or full-enumeration claim is made for these infrastructure results.

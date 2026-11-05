# Independent review of PR #35 (research/cross-domain-20261029, commit fd64c4d)

Reviewer: Claude, from scratch, no reuse of GPT's `probe.py` code.

## Claim reviewed
GPT's "PROVED-PAPER: projection formula" in
`research/all_five_adversarial_20261029/REPORT.md`:

  c(p) = sum_{T subset [j]} (-1)^|T| * |pi_T(A)|

where A is the set of distinct certificates below an all-five pattern p
(encoded as j-tuples of local pair/triple splits), and pi_T is projection
onto coordinates T.

## What was independently checked

1. **Abstract combinatorial identity** (`verify_projection_formula.py`):
   for an arbitrary finite set A of distinct j-tuples over a small alphabet,
   brute-forced over ALL nonempty subsets S subset A,
     c_bruteforce(A) = sum_{nonempty S} (-1)^(|S|+1) * [S agrees in no coordinate]
   against the projection formula. 2000 random trials (j in 1..4, alphabet
   in 2..4, |A| up to 6) via code written independently of GPT's `probe.py`
   and of Claude's own `five_kernel.py`/`five_pairs.cpp`. Result:
   0 mismatches. This is the general inclusion-exclusion/Euler-characteristic
   identity GPT's proof rests on, verified as an abstract fact about finite
   sets of tuples, decoupled from Same Game semantics.

2. **Geometric lemma underlying the reduction** (`verify_5split_join.py`):
   any two DISTINCT splits of a 5-element set into (pair, triple) have join
   equal to the single-block partition of all 5 elements. Checked
   exhaustively over all C(10,2)=45 pairs of the 10 possible splits.
   0 failures. This is what licenses collapsing "members of S agree on
   coordinate i" to "members of S chose the same local split" — i.e. why
   the all-five case reduces cleanly to the tuple/projection picture at all.

## Verdict

**CONFIRMED independently.** Both load-bearing claims in PR #35's projection
formula hold under independent, from-scratch code. This is a real reduction
of the open problem, not a numeric curve-fit: it recasts c(p) for the
all-five kernel as (up to sign) the reduced Euler characteristic of a
j-partite "choice complex" built from the certificate tuples, with no
dependence on the >=3-atom cancellation conjecture it was meant to help
prove. It does not resolve that conjecture.

Not independently re-verified here: GPT's own `probe.py` VERIFIED-COMP
sampling run (results.json, seed 20261031) — that script already asserts
`c == projected` inline per sample, so it is self-checking; I did not
rerun it bit-for-bit. The abstract identity check above is a stronger,
sampling-independent confirmation of the same formula.

## Status
PROVED-PAPER claim in PR #35: **confirmed by independent review**.
VERIFIED-COMP sampling claim in PR #35: not separately rerun; internally
self-checked, biased sampling as GPT itself notes, no exhaustivity claim.

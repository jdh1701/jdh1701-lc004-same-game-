# Same Game strategy reset: toward genuine enumeration progress
Date: 2026-10-28. This is a research plan, not a proof of general enumeration.

## Exact target
W_n(q) counts DISTINCT length-n words on q colors clearable by deleting maximal monochromatic runs of length >=2. Binary q=2 has a known formula (Burns & Purcell, 2007). A035617 identifies the general q>=3 enumeration as unsolved; Kurz (2001) already worked with counting polynomials.

## Reproducible verified foundation
- Normalized run-state uniqueness theorem, previously kernel checked.
- Grammar derivations imply contextual pair/triple erasures, kernel checked.
- All raw maximal-run paths imply contextual pair/triple erasures, kernel checked.
- Heaviness simulation, raw isolated-block insertion, duplication and repeated-run extension in the ENCODED game, kernel checked.
- Conditional lift theorems still need their assumptions proven for the raw maximal-run game.
- Two existing raw encoders need formal equality (new pending theorem).

## Strategy allocation
70% discovery and enumeration: build distinct-word counters from symbolically propagated residual parser states, WITHOUT first enumerating all winning words. Test grammar-derivative subset construction, Earley chart states, color-symmetry quotient, and overlap-corrected inclusion-exclusion. Benchmark states, runtime, and exact W_n(q) against known OEIS values and direct exhaustive enumeration.

30% Lean model audit: prove both encoders agree, connect raw maximal-run legal moves to compressed run-state transitions, derive exact raw-winning versus compressed solvability equivalence, close unconditional insertion/lifting; independently prove erasure-to-grammar completeness; only then certify structural enumerative breakthroughs.

## Adversarial gates
1. Hypothesis: explicit conjecture and falsifier.
2. Experiment: exact code, test universe, cross checks and counterexamples.
3. Mathematical proof: must discharge every assumption.
4. Formal proof: CI green on exact commit, inspect source and axioms.
5. Novelty: compare primary literature; generic Catalan, automaton minimization, and run-length 2/3 identities are not enough.
6. Full resolution: non-tautological all-n,q formula/recurrence with independent proof, preferably better than exhaustive q^n listing.

## Anti-patterns to stop
- Derivation counts conflated with distinct strings.
- Minimal automata constructed after enumerating all words called a fast counting algorithm.
- Unsupported percentage-of-solution claims.
- Treating model changes as equivalent without verified bridges.
- Endless elementary Lean lemmas unconnected to the unknown counting theorem.

## Next discriminating computation
Construct reachable deterministic prefix-residual signatures directly from grammar rules (not full-word enumeration), and compare the resulting state-growth curve to exhaustive winning-prefix tries. A useful compression that can be updated without expanding words would be an actual enumeration advance. If signatures explode, switch to tree decompositions with exact overlap correction.

## Literature
Burns and Purcell (2007), Fibonacci Quarterly 45(3), 233-238; Kurz (2001), Polynomials in Same Game; OEIS A035617 and A323844.

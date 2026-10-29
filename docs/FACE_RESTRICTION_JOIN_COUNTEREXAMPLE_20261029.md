# A minimal obstruction to restriction preserving equivalence joins

Date: 2026-10-29. Mathematical counterexample; Lean encoding pending.

Take positions `{0,1,2}`. Let `p` identify 0 with 1 and leave 2 separate. Let `q` identify 1 with 2 and leave 0 separate. Let `e` select positions `{0,2}`.

- `p ⊔ q` is the indiscrete equivalence relation on all three positions by transitivity, so its restriction identifies 0 and 2.
- `restrict(p,e)` and `restrict(q,e)` are each discrete on the two selected positions. Their join remains discrete.

Thus `restrict(p ⊔ q,e) ≠ restrict(p,e) ⊔ restrict(q,e)`.

## Consequence
The unconditional commuting-join theorem is false. Any Face Lemma requiring it needs a closure condition excluding equivalence paths that leave a face and return. In graph terms, each connected component of the union of constraint edges must intersect a face in a set whose connectivity can already be witnessed internally to that face. This criterion must be made precise before it can be promoted to a theorem.

## Status
The example is proved by direct equivalence closure reasoning, but no new Lean certificate is claimed here. The previous face restriction module is awaiting hosted CI.

## Discriminating next test
Formalize `Fin 3` relations in Lean, evaluate their join and restriction on `Fin 2`, and prove inequality by evaluation. Then prove a corrected conditional theorem under a face-saturation or path-closure hypothesis.

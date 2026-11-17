# Face path-locality research obligation

For equivalence relations p,q on Fin n, let E(a,b) := p(a,b) or q(a,b). The reflexive-transitive closure E* is the join p ⊔ q, since E is symmetric and the closure is an equivalence relation.

For a selected face e : Fin m → Fin n, define local join L := restrict(p,e) ⊔ restrict(q,e).

**Non-tautological sufficient condition:** every E*-path connecting e(i) to e(j) can be replaced by a chain of p/q edges whose vertices lie in the image of e. For injective e, this gives the missing reverse inequality restrict(p ⊔ q,e) ≤ L.

The condition is stronger than necessary but has a geometric interpretation: no essential equivalence path may leave the face and return. The three-vertex path 0--1--2 with face {0,2} violates it.

Lean formalization plan:
1. Define E and Relation.ReflTransGen E.
2. Prove E* equals p ⊔ q using symmetric transitive closure.
3. Define internal paths on Fin m and a path-lifting/replacement hypothesis.
4. Prove restriction commutes with join under this hypothesis.
5. Test whether actual heavy certificates enforce the hypothesis.

No Lean proof is claimed in this note; it is a precise target to avoid unverified complicated proof scripts.

# Retained failed shortcut

The following tempting local lemma is false: if the two five-state pair blocks
are disjoint and adjacent, a is compatible with a six triple T, b is compatible
with both matchings M,N sharing P, and T splits P, then b is compatible with T.

Take five positions (0,1,2,5,6), six positions (3,4,7,8,9,10), and use the Lean
catalogue order: a=0, b=2, M=2, N=3, T=5. The boundary rows are
(255,12,12,12,12). The pair blocks of a,b are (5,6) and (0,1), both adjacent and
disjoint. T splits the matchings' shared six pair, but b does not allow T.

The counterexample has a five-class three-run and many complete certificates;
it does not contradict the final theorem. Simply discarding it using those
observations would not prove the false local assertion. Section 9 instead
constructs a third outside assignment using the four-gap geometry under the
new, uniform two-assignment theorem. check.py retains and rechecks the witness.

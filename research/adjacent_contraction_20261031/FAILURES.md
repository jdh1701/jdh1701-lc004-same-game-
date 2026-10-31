# Attempts and boundaries

- The previous conditional +1 inflation branch is now excluded for nontrivial
  connected all-five complete two-generator full-join sources, by contraction.
  The abstract four-generator lemma was not false and is retained.
- Dropping connectedness or the multiclass assumption is false in general.
  The single-class five-to-six example changes -4 to -1; checks.json retains
  further disconnected examples with nonzero restricted term.
- No local Lean runtime. Compilation attempts and exact hosted source pins are
  recorded here and in receipts.json; no paper proof is upgraded by finite tests.
- Initial local test harness stopped on profile (5,2,3): it compared a canonical
  join partition with a noncanonical generated target labeling. Normalize the
  target at the entry to each test. No mathematical assertion was weakened.
- This work does not establish a constant two two-runs per five-class,
  an exceptional-layer count, or the whole problem. The all-five two-generator
  survival classification was already proved in FiveOriginalCoefficientLaw;
  an initially overcautious draft failed to carry that prior result forward.

Hosted attempt 1: source15c87b88e652f7cb654456aecb0a9532a3376963,
run41209707304. Exact job124561923934 SUCCESS; Lean job124561923620 FAILURE.
Elaboration exposed successor-order obligations, relation reflexivity simplifier
shape mismatches, an unsuccessful reverse sum/card rewrite, untyped uses of
sup inequalities as relation maps, and a final rewrite-generated side goal.
The fixes use explicit relation types, a forward indicator-sum calculation,
typed sup maps, and an explicit final coefficient equality. The complete failed
log is retained. The full axiom audit did not run; failure diagnostics mentioning
sorryAx are compiler placeholders, not accepted proof dependencies.

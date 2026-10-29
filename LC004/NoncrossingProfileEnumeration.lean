import LC004.SingleExceptionalWordCount

namespace LC004
open scoped BigOperators

/-- Restrict the degree-word bijection to any intrinsic profile expressible
through the degree encoding. -/
noncomputable def noncrossingProfileWordEquiv (n : Nat)
    (P : ColorPattern n → Prop) (Q : CyclicDegreeWord n → Prop)
    (hprofile : ∀ p, P p ↔ Q (patternDegreeWord p)) :
    {p : ColorPattern n // PatternNoncrossing p ∧ P p} ≃
    {w : CyclicDegreeWord n // ((∑ i, (w i).val = n) ∧ Q w) ∧ RootedDegreeWord w} where
  toFun p := ⟨patternDegreeWord p.val,
    ⟨patternDegreeWord_sum p.val, (hprofile p.val).mp p.property.2⟩,
    patternDegreeWord_rooted p.val⟩
  invFun w :=
    let p := (noncrossingDegreeWordEquiv n).symm
      ⟨w.val, w.property.1.1, w.property.2⟩
    have hp : patternDegreeWord p.val = w.val := by
      exact congrArg (fun v : {w : CyclicDegreeWord n // (∑ i, (w i).val = n) ∧ RootedDegreeWord w} => v.val)
        ((noncrossingDegreeWordEquiv n).apply_symm_apply
          ⟨w.val, w.property.1.1, w.property.2⟩)
    ⟨p.val, p.property, (hprofile p.val).mpr (by rw [hp]; exact w.property.1.2)⟩
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun q : {p : ColorPattern n // PatternNoncrossing p} => q.val)
      ((noncrossingDegreeWordEquiv n).symm_apply_apply
      ⟨p.val, p.property.1⟩)
  right_inv w := by
    apply Subtype.ext
    exact congrArg (fun v : {w : CyclicDegreeWord n // (∑ i, (w i).val = n) ∧ RootedDegreeWord w} => v.val)
      ((noncrossingDegreeWordEquiv n).apply_symm_apply
      ⟨w.val, w.property.1.1, w.property.2⟩)

open scoped Classical in
theorem fourfold_noncrossing_count_closed (k : Nat) (hk : 1 ≤ k) :
    fourfoldNoncrossingPatternCount (2 * k + 2) = (2 * k + 2).choose (k - 1) := by
  classical
  let P : CyclicDegreeWord (2 * k + 2) → Prop := fun w =>
    (∑ i, (w i).val = 2 * k + 2) ∧ SingleExceptionalWord w 4
  have hrotate : ∀ w r, P (rotateDegreeWord w r) ↔ P w := by
    intro w r
    exact and_congr (by rw [degreeWord_sum_rotate]) (singleExceptionalWord_rotate w 4 r)
  have hmark := marked_rooted_word_card P (fun _ h => h.1) hrotate 4 1
    (fun w h => singleExceptionalWord_arity_card w 4 (by omega) h.2)
  have heq := Fintype.card_congr (noncrossingProfileWordEquiv (2 * k + 2)
    FourfoldPairPattern (fun w => SingleExceptionalWord w 4) fourfold_iff_singleExceptionalWord)
  change fourfoldNoncrossingPatternCount (2 * k + 2) =
    Fintype.card {w : CyclicDegreeWord (2 * k + 2) // P w ∧ RootedDegreeWord w} at heq
  simp only [← Nat.card_eq_fintype_card, Nat.one_mul] at hmark heq
  have hanchored : Nat.card {w : CyclicDegreeWord (2 * k + 2) // P w ∧ (w 0).val = 4} =
      (2 * k + 2).choose (k - 1) := by
    simpa only [← Nat.card_eq_fintype_card] using single_anchored_word_count k hk
  exact heq.trans (hmark.symm.trans hanchored)

#print axioms fourfold_noncrossing_count_closed

end LC004

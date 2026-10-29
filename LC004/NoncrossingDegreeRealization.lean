import LC004.DegreePrefixArithmetic

namespace LC004
open scoped BigOperators

def OpeningDegreeRealizable {n : Nat} (d : Fin n → Nat) : Prop :=
  ∃ p : ColorPattern n, PatternNoncrossing p ∧ ∀ i, patternOpeningDegree p i = d i

theorem openingDegreeRealizable_cast {m n : Nat} (h : m = n) (d : Fin n → Nat) :
    OpeningDegreeRealizable (fun i : Fin m => d (Fin.cast h i)) ↔ OpeningDegreeRealizable d := by
  cases h
  rfl

open scoped Classical in
/-- Every balanced opening-degree vector is realized by a conventional
noncrossing partition. The induction removes its last positive entry
and the following zero entries, then inserts one contiguous class. -/
theorem noncrossing_degree_realization (n : Nat) (d : Fin n → Nat)
    (hsum : ∑ i, d i = n)
    (hprefix : ∀ cut, cut ≤ n → cut ≤ degreePrefix d cut) :
    OpeningDegreeRealizable d := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨⊤, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    · have hpos : 0 < ∑ i, d i := by omega
      obtain ⟨i, hi, hsupport⟩ := exists_last_positive_degree d hpos
      let gap := i.val
      let k := d i
      let m := n - k
      have hmass : degreePrefix d gap + k = n :=
        (degree_sum_last_support d i hsupport).symm.trans hsum
      have hkn : k ≤ n := by omega
      have hmn : m ≤ n := Nat.sub_le n k
      have hmass' : degreePrefix d gap = m := by dsimp [m]; omega
      have hgap : gap ≤ m := by
        have h := hprefix gap (Nat.le_of_lt i.isLt)
        omega
      let g : Fin m → Nat := degreeTruncate d hmn gap
      have hgSum : ∑ j, g j = m := by
        rw [← degreePrefix_total]
        change degreePrefix (degreeTruncate d hmn gap) m = m
        rw [degreeTruncate_prefix d hmn gap hgap m, min_eq_right hgap, hmass']
      have hgPrefix : ∀ cut, cut ≤ m → cut ≤ degreePrefix g cut := by
        intro cut hcut
        change cut ≤ degreePrefix (degreeTruncate d hmn gap) cut
        rw [degreeTruncate_prefix d hmn gap hgap cut]
        by_cases hc : cut ≤ gap
        · rw [min_eq_left hc]
          exact hprefix cut (hcut.trans hmn)
        · rw [min_eq_right (by omega), hmass']
          exact hcut
      obtain ⟨p, hp, hdegree⟩ := ih m (by dsimp [m, k]; omega) g hgSum hgPrefix
      have hlen : m + k = n := Nat.sub_add_cancel hkn
      have hbuild : OpeningDegreeRealizable (fun x : Fin (m + k) => d (Fin.cast hlen x)) := by
        refine ⟨insertPatternInterval (k := k) p gap hgap,
          insertPatternInterval_noncrossing p hp gap hgap, ?_⟩
        intro x
        by_cases hx : InFreshInterval gap x
        · rw [inserted_fresh_opening_degree p gap hgap hi x hx]
          by_cases heq : x.val = gap
          · rw [if_pos heq]
            have hxi : Fin.cast hlen x = i := Fin.ext heq
            exact (congrArg d hxi).symm
          · rw [if_neg heq]
            have hix : i < Fin.cast hlen x := by
              change i.val < x.val
              exact lt_of_le_of_ne hx.1 (Ne.symm heq)
            exact (hsupport _ hix).symm
        · let j := survivingPosition gap hgap x hx
          have hback : oldPosition gap k j = x := oldPosition_surviving gap hgap x hx
          rw [← hback, inserted_old_opening_degree, hdegree j]
          change (if j.val < gap then d (Fin.castLE hmn j) else 0) =
            d (Fin.cast hlen (oldPosition gap k j))
          by_cases hj : j.val < gap
          · rw [if_pos hj]
            congr 1
            apply Fin.ext
            simp only [Fin.coe_cast, Fin.coe_castLE, oldPosition, shiftAfterInsertion, if_pos hj]
          · rw [if_neg hj]
            apply Eq.symm
            apply hsupport
            change i.val < (oldPosition gap k j).val
            change gap < shiftAfterInsertion gap k j.val
            unfold shiftAfterInsertion
            rw [if_neg hj]
            dsimp [k] at *
            omega
      exact (openingDegreeRealizable_cast hlen d).mp hbuild

#print axioms noncrossing_degree_realization

end LC004

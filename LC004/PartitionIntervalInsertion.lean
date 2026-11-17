import LC004.NoncrossingDegreeInjective

namespace LC004

def InFreshInterval {n k : Nat} (gap : Nat) (i : Fin (n + k)) : Prop :=
  gap ≤ i.val ∧ i.val < gap + k

instance {n k : Nat} (gap : Nat) (i : Fin (n + k)) : Decidable (InFreshInterval gap i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def survivingPosition {n k : Nat} (gap : Nat) (hgap : gap ≤ n)
    (i : Fin (n + k)) (hi : ¬ InFreshInterval gap i) : Fin n :=
  ⟨if i.val < gap then i.val else i.val - k, by
    have hn := i.isLt
    unfold InFreshInterval at hi
    split_ifs <;> omega⟩

theorem oldPosition_not_fresh {n k : Nat} (gap : Nat) (i : Fin n) :
    ¬ InFreshInterval gap (oldPosition gap k i) := by
  change ¬ (gap ≤ shiftAfterInsertion gap k i.val ∧
    shiftAfterInsertion gap k i.val < gap + k)
  unfold shiftAfterInsertion
  split_ifs <;> omega

theorem survivingPosition_old {n k : Nat} (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    survivingPosition gap hgap (oldPosition gap k i) (oldPosition_not_fresh gap i) = i := by
  apply Fin.ext
  change (if shiftAfterInsertion gap k i.val < gap then
    shiftAfterInsertion gap k i.val else shiftAfterInsertion gap k i.val - k) = i.val
  unfold shiftAfterInsertion
  split_ifs <;> omega

theorem oldPosition_surviving {n k : Nat} (gap : Nat) (hgap : gap ≤ n)
    (i : Fin (n + k)) (hi : ¬ InFreshInterval gap i) :
    oldPosition gap k (survivingPosition gap hgap i hi) = i := by
  apply Fin.ext
  have hn := i.isLt
  unfold InFreshInterval at hi
  change shiftAfterInsertion gap k (if i.val < gap then i.val else i.val - k) = i.val
  unfold shiftAfterInsertion
  split_ifs <;> omega

theorem oldPosition_lt_iff {n k : Nat} (gap : Nat) (i j : Fin n) :
    oldPosition gap k i < oldPosition gap k j ↔ i < j := by
  change shiftAfterInsertion gap k i.val < shiftAfterInsertion gap k j.val ↔ i.val < j.val
  unfold shiftAfterInsertion
  split_ifs <;> omega

noncomputable def intervalInsertionLabel {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin (n + k)) : Option (Quotient p) :=
  if hi : InFreshInterval gap i then none
  else some (Quotient.mk p (survivingPosition gap hgap i hi))

noncomputable def insertPatternInterval {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) : ColorPattern (n + k) :=
  Setoid.ker (intervalInsertionLabel p gap hgap)

theorem intervalInsertionLabel_old {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    intervalInsertionLabel p gap hgap (oldPosition gap k i) = some (Quotient.mk p i) := by
  rw [intervalInsertionLabel, dif_neg (oldPosition_not_fresh gap i), survivingPosition_old]

theorem intervalInsertionLabel_none_iff {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin (n + k)) :
    intervalInsertionLabel p gap hgap i = none ↔ InFreshInterval gap i := by
  unfold intervalInsertionLabel
  split_ifs <;> simp_all

theorem insertPatternInterval_old_rel {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i j : Fin n) :
    insertPatternInterval p gap hgap (oldPosition gap k i) (oldPosition gap k j) ↔ p i j := by
  change intervalInsertionLabel p gap hgap (oldPosition gap k i) =
    intervalInsertionLabel p gap hgap (oldPosition gap k j) ↔ _
  rw [intervalInsertionLabel_old, intervalInsertionLabel_old, Option.some.injEq]
  exact ⟨Quotient.exact, Quotient.sound⟩

theorem insertPatternInterval_fresh_rel {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i j : Fin (n + k))
    (hi : InFreshInterval gap i) :
    insertPatternInterval p gap hgap i j ↔ InFreshInterval gap j := by
  change intervalInsertionLabel p gap hgap i = intervalInsertionLabel p gap hgap j ↔ _
  rw [(intervalInsertionLabel_none_iff p gap hgap i).mpr hi]
  exact eq_comm.trans (intervalInsertionLabel_none_iff p gap hgap j)

/-- Inserting an entire new interval class preserves conventional NC,
with no bound of three on the size of the inserted coarse class. -/
theorem insertPatternInterval_noncrossing {n k : Nat} (p : ColorPattern n)
    (hp : PatternNoncrossing p) (gap : Nat) (hgap : gap ≤ n) :
    PatternNoncrossing (insertPatternInterval (k := k) p gap hgap) := by
  intro a b c d hab hbc hcd hac hbd
  by_cases ha : InFreshInterval gap a
  · have hc := (insertPatternInterval_fresh_rel p gap hgap a c ha).mp hac
    have hb : InFreshInterval gap b := by
      unfold InFreshInterval at *
      change a.val < b.val at hab
      change b.val < c.val at hbc
      omega
    exact (insertPatternInterval_fresh_rel p gap hgap a b ha).mpr hb
  · have hc : ¬ InFreshInterval gap c := by
      intro hf
      exact ha ((insertPatternInterval_fresh_rel p gap hgap c a hf).mp
        ((insertPatternInterval p gap hgap).symm hac))
    by_cases hb : InFreshInterval gap b
    · have hd := (insertPatternInterval_fresh_rel p gap hgap b d hb).mp hbd
      have hf : InFreshInterval gap c := by
        unfold InFreshInterval at *
        change b.val < c.val at hbc
        change c.val < d.val at hcd
        omega
      exact (hc hf).elim
    · have hd : ¬ InFreshInterval gap d := by
        intro hf
        exact hb ((insertPatternInterval_fresh_rel p gap hgap d b hf).mp
          ((insertPatternInterval p gap hgap).symm hbd))
      let a' := survivingPosition gap hgap a ha
      let b' := survivingPosition gap hgap b hb
      let c' := survivingPosition gap hgap c hc
      let d' := survivingPosition gap hgap d hd
      have ha' : oldPosition gap k a' = a := oldPosition_surviving gap hgap a ha
      have hb' : oldPosition gap k b' = b := oldPosition_surviving gap hgap b hb
      have hc' : oldPosition gap k c' = c := oldPosition_surviving gap hgap c hc
      have hd' : oldPosition gap k d' = d := oldPosition_surviving gap hgap d hd
      have hab' : a' < b' := (oldPosition_lt_iff (k := k) gap a' b').mp (by simpa [ha', hb'] using hab)
      have hbc' : b' < c' := (oldPosition_lt_iff (k := k) gap b' c').mp (by simpa [hb', hc'] using hbc)
      have hcd' : c' < d' := (oldPosition_lt_iff (k := k) gap c' d').mp (by simpa [hc', hd'] using hcd)
      have hac' : p a' c' := (insertPatternInterval_old_rel (k := k) p gap hgap a' c').mp
        (by simpa [ha', hc'] using hac)
      have hbd' : p b' d' := (insertPatternInterval_old_rel (k := k) p gap hgap b' d').mp
        (by simpa [hb', hd'] using hbd)
      have habrel := hp a' b' c' d' hab' hbc' hcd' hac' hbd'
      have h := (insertPatternInterval_old_rel (k := k) p gap hgap a' b').mpr habrel
      simpa [ha', hb'] using h

#print axioms insertPatternInterval_noncrossing

end LC004

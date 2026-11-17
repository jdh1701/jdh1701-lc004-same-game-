import LC004.WitnessEmbedding
import LC004.QuadWitnessClassification

namespace LC004

theorem quadPosition_strictMono {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrictMono (quadPosition a b c d) := by
  intro i j hij
  unfold quadPosition
  split_ifs <;> simp_all <;> omega

@[simp] theorem quadSplitEquiv_symm_selected {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (i : Fin 4) :
    (quadSplitEquiv a b c d hab hbc hcd).symm (Sum.inl i) = quadPosition a b c d i := rfl

@[simp] theorem quadSplitEquiv_symm_remainder {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (x : QuadRemainder a b c d) :
    (quadSplitEquiv a b c d hab hbc hcd).symm (Sum.inr x) = x.val := rfl

set_option maxHeartbeats 800000 in
theorem quad_adjacent_barrier {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      (quadAdjacent,adjacentGapRegions (remainderGapIndex a b c d)) =
      pairGapPartition a b ⊓ pairGapPartition c d := by
  let e := quadSplitEquiv a b c d hab hbc hcd
  apply Setoid.ext
  intro x y
  obtain ⟨x,rfl⟩ := e.symm.surjective x
  obtain ⟨y,rfl⟩ := e.symm.surjective y
  change fullBoardPartition e _ (e.symm x) (e.symm y) ↔ _
  simp only [fullBoardPartition_rel,Equiv.apply_symm_apply]
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp only [Sum.liftRel_inl_inl]
      change quadAdjacent i j ↔
        (pairGapPartition a b ⊓ pairGapPartition c d)
          (quadPosition a b c d i) (quadPosition a b c d j)
      fin_cases i <;> fin_cases j <;>
        simp [quadAdjacent,quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and] <;>
        split_ifs <;> simp_all <;> omega
    | inr y =>
      obtain ⟨hya,hyb,hyc,hyd⟩ := y.property
      simp only [Sum.not_liftRel_inl_inr,false_iff]
      change ¬(pairGapPartition a b ⊓ pairGapPartition c d)
        (quadPosition a b c d i) y.val
      fin_cases i <;>
        simp [quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and,hya,hyb,hyc,hyd] <;>
        split_ifs <;> simp_all
  | inr x =>
    cases y with
    | inl j =>
      obtain ⟨hxa,hxb,hxc,hxd⟩ := x.property
      simp only [Sum.not_liftRel_inr_inl,false_iff]
      change ¬(pairGapPartition a b ⊓ pairGapPartition c d)
        x.val (quadPosition a b c d j)
      fin_cases j <;>
        simp [quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and,hxa,hxb,hxc,hxd] <;>
        split_ifs <;> simp_all
    | inr y =>
      simp only [Sum.liftRel_inr_inr]
      exact (Setoid.ext_iff.mp (adjacent_pair_remainder_regions a b c d hab hbc hcd) x y).symm

set_option maxHeartbeats 800000 in
theorem quad_nested_barrier {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    fullBoardPartition (quadSplitEquiv a b c d hab hbc hcd)
      (quadNested,nestedGapRegions (remainderGapIndex a b c d)) =
      pairGapPartition a d ⊓ pairGapPartition b c := by
  let e := quadSplitEquiv a b c d hab hbc hcd
  apply Setoid.ext
  intro x y
  obtain ⟨x,rfl⟩ := e.symm.surjective x
  obtain ⟨y,rfl⟩ := e.symm.surjective y
  change fullBoardPartition e _ (e.symm x) (e.symm y) ↔ _
  simp only [fullBoardPartition_rel,Equiv.apply_symm_apply]
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp only [Sum.liftRel_inl_inl]
      change quadNested i j ↔
        (pairGapPartition a d ⊓ pairGapPartition b c)
          (quadPosition a b c d i) (quadPosition a b c d j)
      fin_cases i <;> fin_cases j <;>
        simp [quadNested,quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and] <;>
        split_ifs <;> simp_all <;> omega
    | inr y =>
      obtain ⟨hya,hyb,hyc,hyd⟩ := y.property
      simp only [Sum.not_liftRel_inl_inr,false_iff]
      change ¬(pairGapPartition a d ⊓ pairGapPartition b c)
        (quadPosition a b c d i) y.val
      fin_cases i <;>
        simp [quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and,hya,hyb,hyc,hyd] <;>
        split_ifs <;> simp_all
  | inr x =>
    cases y with
    | inl j =>
      obtain ⟨hxa,hxb,hxc,hxd⟩ := x.property
      simp only [Sum.not_liftRel_inr_inl,false_iff]
      change ¬(pairGapPartition a d ⊓ pairGapPartition b c)
        x.val (quadPosition a b c d j)
      fin_cases j <;>
        simp [quadPosition,pairGapPartition,Setoid.ker_def,Setoid.inf_iff_and,hxa,hxb,hxc,hxd] <;>
        split_ifs <;> simp_all
    | inr y =>
      simp only [Sum.liftRel_inr_inr]
      exact (Setoid.ext_iff.mp (nested_pair_remainder_regions a b c d hab hbc hcd) x y).symm

end LC004

import LC004.ChordBarrier

namespace LC004

/-- The entire equivalence class of `a` consists of the two endpoints. -/
def IsPairBlock {α : Type*} (r : Setoid α) (a b : α) : Prop :=
  ∀ x, r a x ↔ x = a ∨ x = b

/-- Three regions: the endpoints, their strict interior, and the exterior.
The exterior can contain positions both before `a` and after `b`. -/
def pairGapPartition {n : Nat} (a b : Fin n) : Setoid (Fin n) :=
  Setoid.ker (fun x =>
    if x = a ∨ x = b then (0 : Nat)
    else if a < x ∧ x < b then 1 else 2)

/-- The chord together with its inside and outside regions is noncrossing. -/
theorem pairGapPartition_noncrossing {n : Nat} (a b : Fin n) (hab : a < b) :
    IsNoncrossing (pairGapPartition a b) := by
  intro w x y z hwx hxy hyz hwy hxz
  simp only [pairGapPartition, Setoid.ker_def] at hwy hxz ⊢
  split_ifs at * <;> omega

/-- An actual noncrossing witness with the indicated pair refines its three
regions. No gap-separation hypothesis is assumed here. -/
theorem forced_pair_refines_gaps {n : Nat}
    (r : Setoid (Fin n)) (hr : IsNoncrossing r) (a b : Fin n)
    (hp : IsPairBlock r a b) : r ≤ pairGapPartition a b := by
  intro x y hxy
  have hpair : r a b := (hp b).mpr (Or.inr rfl)
  have hend : (x = a ∨ x = b) ↔ (y = a ∨ y = b) := by
    constructor
    · intro hx
      exact (hp y).mp (r.trans ((hp x).mpr hx) hxy)
    · intro hy
      exact (hp x).mp (r.trans ((hp y).mpr hy) (r.symm hxy))
  change (if x = a ∨ x = b then (0 : Nat)
      else if a < x ∧ x < b then 1 else 2) =
    (if y = a ∨ y = b then 0 else if a < y ∧ y < b then 1 else 2)
  by_cases hx : x = a ∨ x = b
  · simp [hx, hend.mp hx]
  · have hy : ¬(y = a ∨ y = b) := fun hy => hx (hend.mpr hy)
    have hax : ¬r a x := fun h => hx ((hp x).mp h)
    have hay : ¬r a y := fun h => hy ((hp y).mp h)
    have hi := noncrossing_interval_barrier r hr a b x y hpair hxy hax hay
    simp only [if_neg hx, if_neg hy]
    simp only [hi]

/-- Common refinement preserves noncrossing, unlike the join of partitions. -/
theorem noncrossing_inf {α : Type*} [LinearOrder α]
    (r s : Setoid α) (hr : IsNoncrossing r) (hs : IsNoncrossing s) :
    IsNoncrossing (r ⊓ s) := by
  intro a b c d hab hbc hcd hac hbd
  exact ⟨hr a b c d hab hbc hcd hac.1 hbd.1,
    hs a b c d hab hbc hcd hac.2 hbd.2⟩

/-- Exact witness decomposition at a forced pair. The reverse direction
reconstructs global noncrossing and block sizes from the regional conditions. -/
theorem forced_pair_gap_decomposition {n : Nat}
    (r : Setoid (Fin n)) (a b : Fin n) (hab : a < b)
    (hp : IsPairBlock r a b) :
    PairTriplePartition r ↔
      r ≤ pairGapPartition a b ∧
      ∀ x, PairTriplePartition (restrictToBlock r (pairGapPartition a b) x) := by
  have hs := pairGapPartition_noncrossing a b hab
  constructor
  · intro hr
    have hrs := forced_pair_refines_gaps r hr.1 a b hp
    exact ⟨hrs, (pairTriple_iff_blocks r _ hrs hs).mp hr⟩
  · rintro ⟨hrs, h⟩
    exact (pairTriple_iff_blocks r _ hrs hs).mpr h

/-- Two forced chords separate a witness into the common refinement of their
regions. Applied to (a,b),(c,d) this gives the adjacent-pairing gaps; applied
to (a,d),(b,c) it gives the nested-pairing gaps. -/
theorem forced_two_pair_gap_decomposition {n : Nat}
    (r : Setoid (Fin n)) (a b c d : Fin n) (hab : a < b) (hcd : c < d)
    (hp : IsPairBlock r a b) (hq : IsPairBlock r c d) :
    PairTriplePartition r ↔
      r ≤ pairGapPartition a b ⊓ pairGapPartition c d ∧
      ∀ x, PairTriplePartition
        (restrictToBlock r (pairGapPartition a b ⊓ pairGapPartition c d) x) := by
  have hs := noncrossing_inf _ _
    (pairGapPartition_noncrossing a b hab) (pairGapPartition_noncrossing c d hcd)
  constructor
  · intro hr
    have hrs := le_inf (forced_pair_refines_gaps r hr.1 a b hp)
      (forced_pair_refines_gaps r hr.1 c d hq)
    exact ⟨hrs, (pairTriple_iff_blocks r _ hrs hs).mp hr⟩
  · rintro ⟨hrs, h⟩
    exact (pairTriple_iff_blocks r _ hrs hs).mpr h

end LC004

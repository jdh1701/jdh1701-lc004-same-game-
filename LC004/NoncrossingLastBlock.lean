import LC004.PartitionOpeningMass

namespace LC004

noncomputable def patternClassLeader {n : Nat} (p : ColorPattern n) (i : Fin n) : Fin n :=
  patternClassMinimum p (Quotient.mk p i)

theorem patternClassLeader_le {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternClassLeader p i ≤ i := patternClassMinimum_le p i

theorem patternClassLeader_related {n : Nat} (p : ColorPattern n) (i : Fin n) :
    p (patternClassLeader p i) i :=
  Quotient.exact (patternClassMinimum_quotient p (Quotient.mk p i))

theorem patternClassLeader_idempotent {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternClassLeader p (patternClassLeader p i) = patternClassLeader p i := by
  unfold patternClassLeader
  rw [patternClassMinimum_quotient]

theorem pattern_related_iff_leaders {n : Nat} (p : ColorPattern n) (i j : Fin n) :
    p i j ↔ patternClassLeader p i = patternClassLeader p j := by
  constructor
  · intro h
    exact congrArg (patternClassMinimum p) (Quotient.sound h)
  · intro h
    exact Quotient.exact (patternClassMinimum_injective p h)

theorem opening_degree_pos_iff_leader {n : Nat} (p : ColorPattern n) (i : Fin n) :
    0 < patternOpeningDegree p i ↔ patternClassLeader p i = i := by
  classical
  rw [patternOpeningDegree_eq]
  change (0 < if patternClassLeader p i = i then
    (patternClassPositions p i).card else 0) ↔ _
  split_ifs with h
  · have hm : i ∈ patternClassPositions p i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.refl i⟩
    exact ⟨fun _ => h, fun _ => Finset.card_pos.mpr ⟨i, hm⟩⟩
  · simp [h]

/-- The class with the last first occurrence cannot have a gap. -/
theorem last_opened_class_interval {n : Nat} (p : ColorPattern n)
    (hnc : PatternNoncrossing p) (q : Quotient p)
    (hlast : ∀ r, patternClassMinimum p r ≤ patternClassMinimum p q)
    (i j : Fin n) (hmin : patternClassMinimum p q ≤ i) (hij : i ≤ j)
    (hj : Quotient.mk p j = q) : Quotient.mk p i = q := by
  by_contra hi
  let r := Quotient.mk p i
  have hri : p (patternClassMinimum p r) i := patternClassLeader_related p i
  have hqj : p (patternClassMinimum p q) j :=
    Quotient.exact ((patternClassMinimum_quotient p q).trans hj.symm)
  have hrq : patternClassMinimum p r ≠ patternClassMinimum p q := by
    intro h
    exact hi (patternClassMinimum_injective p h)
  have hlt : patternClassMinimum p r < patternClassMinimum p q :=
    lt_of_le_of_ne (hlast r) hrq
  have hmi : patternClassMinimum p q < i := by
    apply lt_of_le_of_ne hmin
    intro h
    exact hi (h ▸ patternClassMinimum_quotient p q)
  have hij' : i < j := by
    apply lt_of_le_of_ne hij
    intro h
    exact hi ((congrArg (Quotient.mk p) h).trans hj)
  have hcross := hnc (patternClassMinimum p r) (patternClassMinimum p q) i j
    hlt hmi hij' hri hqj
  have hrq' : r = q := (patternClassMinimum_quotient p r).symm.trans
    ((Quotient.sound hcross).trans (patternClassMinimum_quotient p q))
  exact hi hrq'

theorem exists_last_opened_class {n : Nat} (p : ColorPattern n) (hn : 0 < n) :
    ∃ q : Quotient p, ∀ r, patternClassMinimum p r ≤ patternClassMinimum p q := by
  classical
  have he : (Finset.univ : Finset (Quotient p)).Nonempty :=
    ⟨Quotient.mk p ⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_max_image Finset.univ (patternClassMinimum p) he
  exact ⟨q, fun r => hq r (Finset.mem_univ r)⟩

noncomputable def patternClassMaximum {n : Nat} (p : ColorPattern n)
    (q : Quotient p) : Fin n := by
  classical
  exact (patternQuotientFiber p q).max' ⟨patternClassMinimum p q,
    patternClassMinimum_mem p q⟩

theorem patternClassMaximum_mem {n : Nat} (p : ColorPattern n) (q : Quotient p) :
    patternClassMaximum p q ∈ patternQuotientFiber p q := by
  classical
  exact Finset.max'_mem _ _

open scoped Classical in
theorem last_opened_class_eq_interval {n : Nat} (p : ColorPattern n)
    (hnc : PatternNoncrossing p) (q : Quotient p)
    (hlast : ∀ r, patternClassMinimum p r ≤ patternClassMinimum p q) :
    patternQuotientFiber p q =
      Finset.Icc (patternClassMinimum p q) (patternClassMaximum p q) := by
  classical
  ext i
  constructor
  · intro hi
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ i hi, Finset.le_max' _ i hi⟩
  · intro hi
    obtain ⟨hmin, hmax⟩ := Finset.mem_Icc.mp hi
    have hm := (Finset.mem_filter.mp (patternClassMaximum_mem p q)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      last_opened_class_interval p hnc q hlast i (patternClassMaximum p q) hmin hmax hm⟩

#print axioms last_opened_class_eq_interval

end LC004

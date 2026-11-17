import LC004.PartitionIntervalInsertion

namespace LC004

theorem patternClassLeader_eq_of_least {n : Nat} (p : ColorPattern n) (i a : Fin n)
    (hai : p a i) (hmin : ∀ j, p j i → a ≤ j) : patternClassLeader p i = a := by
  apply le_antisymm
  · have h := (pattern_related_iff_leaders p a i).mp hai
    rw [← h]
    exact patternClassLeader_le p a
  · exact hmin _ (patternClassLeader_related p i)

open scoped Classical in
theorem inserted_old_class_positions {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    patternClassPositions (insertPatternInterval p gap hgap) (oldPosition gap k i) =
      (patternClassPositions p i).image (oldPosition gap k) := by
  classical
  ext j
  constructor
  · intro hj
    have hrel := (Finset.mem_filter.mp hj).2
    have hnf : ¬ InFreshInterval gap j := by
      intro hf
      have hold := (insertPatternInterval_fresh_rel p gap hgap j (oldPosition gap k i) hf).mp
        ((insertPatternInterval p gap hgap).symm hrel)
      exact oldPosition_not_fresh gap i hold
    let j' := survivingPosition gap hgap j hnf
    have hback : oldPosition gap k j' = j := oldPosition_surviving gap hgap j hnf
    refine Finset.mem_image.mpr ⟨j', ?_, hback⟩
    have h := (insertPatternInterval_old_rel (k := k) p gap hgap i j').mp
      (by simpa only [hback] using hrel)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · intro hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (insertPatternInterval_old_rel (k := k) p gap hgap i j').mpr (Finset.mem_filter.mp hj').2⟩

theorem inserted_old_class_card {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    (patternClassPositions (insertPatternInterval p gap hgap) (oldPosition gap k i)).card =
      (patternClassPositions p i).card := by
  classical
  rw [inserted_old_class_positions, Finset.card_image_of_injective _ (oldPosition_injective gap k)]

open scoped Classical in
theorem fresh_interval_positions {n k : Nat} (gap : Nat) (hgap : gap ≤ n) :
    (Finset.univ : Finset (Fin (n + k))).filter (InFreshInterval gap) =
      (Finset.univ : Finset (Fin k)).image (freshPosition gap k hgap) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hj
    let s : Fin k := ⟨j.val - gap, by unfold InFreshInterval at hj; omega⟩
    refine ⟨s, ?_⟩
    apply Fin.ext
    change gap + (j.val - gap) = j.val
    unfold InFreshInterval at hj
    omega
  · rintro ⟨s, _, rfl⟩
    unfold InFreshInterval freshPosition
    have hs := s.isLt
    simp only
    omega

theorem inserted_fresh_class_card {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin (n + k)) (hi : InFreshInterval gap i) :
    (patternClassPositions (insertPatternInterval p gap hgap) i).card = k := by
  classical
  have heq : patternClassPositions (insertPatternInterval p gap hgap) i =
      Finset.univ.filter (InFreshInterval gap) := by
    ext j
    simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact insertPatternInterval_fresh_rel p gap hgap i j hi
  rw [heq, fresh_interval_positions gap hgap,
    Finset.card_image_of_injective _ (freshPosition_injective gap k hgap),
    Finset.card_univ, Fintype.card_fin]

theorem inserted_old_class_leader {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    patternClassLeader (insertPatternInterval p gap hgap) (oldPosition gap k i) =
      oldPosition gap k (patternClassLeader p i) := by
  classical
  apply patternClassLeader_eq_of_least
  · exact (insertPatternInterval_old_rel (k := k) p gap hgap _ _).mpr (patternClassLeader_related p i)
  · intro j hj
    have hmem : j ∈ patternClassPositions (insertPatternInterval p gap hgap)
        (oldPosition gap k i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (insertPatternInterval p gap hgap).symm hj⟩
    rw [inserted_old_class_positions] at hmem
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hmem
    have hrel : p i j' := (Finset.mem_filter.mp hj').2
    have hlead := (pattern_related_iff_leaders p i j').mp hrel
    have hle : patternClassLeader p i ≤ j' := by
      rw [hlead]
      exact patternClassLeader_le p j'
    by_contra h
    have hlt : oldPosition gap k j' < oldPosition gap k (patternClassLeader p i) :=
      lt_of_not_ge h
    have hlt' := (oldPosition_lt_iff (k := k) gap j' (patternClassLeader p i)).mp hlt
    exact (not_lt_of_ge hle) hlt'

theorem inserted_fresh_class_leader {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (hk : 0 < k)
    (i : Fin (n + k)) (hi : InFreshInterval gap i) :
    patternClassLeader (insertPatternInterval p gap hgap) i =
      freshPosition gap k hgap ⟨0, hk⟩ := by
  have hfirst : InFreshInterval gap (freshPosition gap k hgap ⟨0, hk⟩) := by
    unfold InFreshInterval freshPosition
    simp only [Nat.add_zero]
    omega
  apply patternClassLeader_eq_of_least
  · exact (insertPatternInterval_fresh_rel p gap hgap _ i hfirst).mpr hi
  · intro j hj
    have hjfresh := (insertPatternInterval_fresh_rel p gap hgap i j hi).mp
      ((insertPatternInterval p gap hgap).symm hj)
    change gap + 0 ≤ j.val
    exact by simpa only [Nat.add_zero] using hjfresh.1

theorem inserted_old_opening_degree {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (i : Fin n) :
    patternOpeningDegree (insertPatternInterval p gap hgap) (oldPosition gap k i) =
      patternOpeningDegree p i := by
  classical
  rw [patternOpeningDegree_eq, patternOpeningDegree_eq, inserted_old_class_card]
  change (if patternClassLeader (insertPatternInterval p gap hgap) (oldPosition gap k i) =
    oldPosition gap k i then _ else 0) =
    (if patternClassLeader p i = i then _ else 0)
  rw [inserted_old_class_leader]
  have hiff : oldPosition gap k (patternClassLeader p i) = oldPosition gap k i ↔
      patternClassLeader p i = i := (oldPosition_injective gap k).eq_iff
  simp only [hiff]

theorem inserted_fresh_opening_degree {n k : Nat} (p : ColorPattern n)
    (gap : Nat) (hgap : gap ≤ n) (hk : 0 < k)
    (i : Fin (n + k)) (hi : InFreshInterval gap i) :
    patternOpeningDegree (insertPatternInterval p gap hgap) i =
      if i.val = gap then k else 0 := by
  classical
  rw [patternOpeningDegree_eq, inserted_fresh_class_card p gap hgap i hi]
  change (if patternClassLeader (insertPatternInterval p gap hgap) i = i then k else 0) = _
  rw [inserted_fresh_class_leader p gap hgap hk i hi]
  have heq : freshPosition gap k hgap ⟨0, hk⟩ = i ↔ i.val = gap := by
    constructor
    · intro h
      have hval := congrArg (fun j : Fin (n + k) => j.val) h
      simpa only [freshPosition, Nat.add_zero] using hval.symm
    · intro h
      apply Fin.ext
      simpa only [freshPosition, Nat.add_zero] using h.symm
  simp only [heq]

#print axioms inserted_old_opening_degree
#print axioms inserted_fresh_opening_degree

end LC004

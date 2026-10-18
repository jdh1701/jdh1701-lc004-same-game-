import LC004.FullBoardCancellation

namespace LC004

theorem noncrossing_comap_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) (r : Setoid β) (hr : IsNoncrossing r) :
    IsNoncrossing (Setoid.comap f r) := by
  intro a b c d hab hbc hcd hac hbd
  exact hr _ _ _ _ (hf hab) (hf hbc) (hf hcd) hac hbd

/-- Pullback along an injection retains block sizes if its image contains
every element of each block it meets. -/
theorem blockSize_comap_saturated {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hf : Function.Injective f) (r : Setoid β)
    (hsat : ∀ a y, r y (f a) → ∃ b, f b = y) (a : α) :
    partitionBlockSize (Setoid.comap f r) a = partitionBlockSize r (f a) := by
  classical
  apply @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
  apply Equiv.ofBijective (fun x => (⟨f x.val,x.property⟩ : {y // r y (f a)}))
  constructor
  · intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  · intro y
    obtain ⟨b,hb⟩ := hsat a y.val y.property
    refine ⟨⟨b,?_⟩,?_⟩
    · change r (f b) (f a)
      simpa only [hb] using y.property
    · exact Subtype.ext hb

theorem pairTriple_comap_saturated {α β : Type*} [LinearOrder α] [LinearOrder β]
    [Finite α] [Finite β] (f : α → β) (hf : StrictMono f) (r : Setoid β)
    (hr : PairTriplePartition r) (hsat : ∀ a y, r y (f a) → ∃ b, f b = y) :
    PairTriplePartition (Setoid.comap f r) := by
  refine ⟨noncrossing_comap_strictMono f hf r hr.1,?_⟩
  intro a
  rw [blockSize_comap_saturated f hf.injective r hsat a]
  exact hr.2 (f a)

@[simp] theorem fullBoardPartition_rel {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (p : Setoid α × Setoid β) (x y : γ) :
    fullBoardPartition e p x y ↔ Sum.LiftRel p.1.r p.2.r (e x) (e y) := Iff.rfl

theorem fullBoardPartition_reconstruct {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (r : Setoid γ) (hr : r ≤ fullBoardPartition e ((⊤ : Setoid α),(⊤ : Setoid β))) :
    fullBoardPartition e
      (Setoid.comap (fun a => e.symm (Sum.inl a)) r,
       Setoid.comap (fun b => e.symm (Sum.inr b)) r) = r := by
  apply Setoid.ext
  intro x y
  obtain ⟨x,rfl⟩ := e.symm.surjective x
  obtain ⟨y,rfl⟩ := e.symm.surjective y
  cases x <;> cases y
  · simp only [fullBoardPartition_rel,Equiv.apply_symm_apply,Sum.liftRel_inl_inl,
      Setoid.comap_rel]
  · simp only [fullBoardPartition_rel,Equiv.apply_symm_apply]
    constructor
    · intro h; cases h
    · intro h; have hh := hr h; simp at hh
  · simp only [fullBoardPartition_rel,Equiv.apply_symm_apply]
    constructor
    · intro h; cases h
    · intro h; have hh := hr h; simp at hh
  · simp only [fullBoardPartition_rel,Equiv.apply_symm_apply,Sum.liftRel_inr_inr,
      Setoid.comap_rel]

theorem fullBoardPartition_left_saturated {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (r : Setoid γ) (hr : r ≤ fullBoardPartition e ((⊤ : Setoid α),(⊤ : Setoid β))) :
    ∀ a y, r y (e.symm (Sum.inl a)) → ∃ b, e.symm (Sum.inl b) = y := by
  intro a y hy
  obtain ⟨z,rfl⟩ := e.symm.surjective y
  cases z with
  | inl b => exact ⟨b,rfl⟩
  | inr b => have h := hr hy; simp at h

theorem fullBoardPartition_right_saturated {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (r : Setoid γ) (hr : r ≤ fullBoardPartition e ((⊤ : Setoid α),(⊤ : Setoid β))) :
    ∀ a y, r y (e.symm (Sum.inr a)) → ∃ b, e.symm (Sum.inr b) = y := by
  intro a y hy
  obtain ⟨z,rfl⟩ := e.symm.surjective y
  cases z with
  | inl b => have h := hr hy; simp at h
  | inr b => exact ⟨b,rfl⟩

/-- A noncrossing coarse barrier prevents crossings between the two parts;
within each part noncrossing is checked in its original order. -/
theorem fullBoardPartition_noncrossing {α β γ : Type*}
    [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (e : γ ≃ α ⊕ β)
    (hf : StrictMono (fun a => e.symm (Sum.inl a)))
    (hg : StrictMono (fun b => e.symm (Sum.inr b)))
    (p : Setoid α × Setoid β) (P : Setoid α × Setoid β)
    (hp : IsNoncrossing p.1) (hq : IsNoncrossing p.2) (hle : p ≤ P)
    (hP : IsNoncrossing (fullBoardPartition e P)) :
    IsNoncrossing (fullBoardPartition e p) := by
  have ht : fullBoardPartition e p ≤ fullBoardPartition e P :=
    (relabelPartitions e).monotone ((separatedPartition_le_separated_iff p P).mpr hle)
  intro a b c d hab hbc hcd hac hbd
  have hAB := hP a b c d hab hbc hcd (ht hac) (ht hbd)
  obtain ⟨a,rfl⟩ := e.symm.surjective a
  obtain ⟨b,rfl⟩ := e.symm.surjective b
  obtain ⟨c,rfl⟩ := e.symm.surjective c
  obtain ⟨d,rfl⟩ := e.symm.surjective d
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [fullBoardPartition_rel,Equiv.apply_symm_apply] at hac hbd hAB ⊢
  all_goals try { cases hac }
  all_goals try { cases hbd }
  all_goals try { cases hAB }
  · exact Sum.LiftRel.inl (hp _ _ _ _ (hf.lt_iff_lt.mp hab)
      (hf.lt_iff_lt.mp hbc) (hf.lt_iff_lt.mp hcd)
      (Sum.liftRel_inl_inl.mp hac) (Sum.liftRel_inl_inl.mp hbd))
  · exact Sum.LiftRel.inr (hq _ _ _ _ (hg.lt_iff_lt.mp hab)
      (hg.lt_iff_lt.mp hbc) (hg.lt_iff_lt.mp hcd)
      (Sum.liftRel_inr_inr.mp hac) (Sum.liftRel_inr_inr.mp hbd))

@[simp] theorem fullBoardPartition_comap_left {α β γ : Type*}
    (e : γ ≃ α ⊕ β) (p : Setoid α × Setoid β) :
    Setoid.comap (fun a => e.symm (Sum.inl a)) (fullBoardPartition e p) = p.1 := by
  apply Setoid.ext
  intro x y
  simp only [Setoid.comap_rel,fullBoardPartition_rel,Equiv.apply_symm_apply,
    Sum.liftRel_inl_inl]
  exact Sum.liftRel_inl_inl

@[simp] theorem fullBoardPartition_comap_right {α β γ : Type*}
    (e : γ ≃ α ⊕ β) (p : Setoid α × Setoid β) :
    Setoid.comap (fun a => e.symm (Sum.inr a)) (fullBoardPartition e p) = p.2 := by
  apply Setoid.ext
  intro x y
  simp only [Setoid.comap_rel,fullBoardPartition_rel,Equiv.apply_symm_apply,
    Sum.liftRel_inr_inr]
  exact Sum.liftRel_inr_inr

theorem fullBoardPartition_pairTriple {α β γ : Type*}
    [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    [Finite α] [Finite β] [Finite γ]
    (e : γ ≃ α ⊕ β)
    (hf : StrictMono (fun a => e.symm (Sum.inl a)))
    (hg : StrictMono (fun b => e.symm (Sum.inr b)))
    (p : Setoid α × Setoid β) (P : Setoid α × Setoid β)
    (hp : PairTriplePartition p.1) (hq : PairTriplePartition p.2) (hle : p ≤ P)
    (hP : IsNoncrossing (fullBoardPartition e P)) :
    PairTriplePartition (fullBoardPartition e p) := by
  refine ⟨fullBoardPartition_noncrossing e hf hg p P hp.1 hq.1 hle hP,?_⟩
  have ht : fullBoardPartition e p ≤ fullBoardPartition e ((⊤ : Setoid α),(⊤ : Setoid β)) :=
    (relabelPartitions e).monotone ((separatedPartition_le_separated_iff _ _).mpr le_top)
  intro x
  obtain ⟨x,rfl⟩ := e.symm.surjective x
  cases x with
  | inl a =>
    have h := blockSize_comap_saturated _ hf.injective _
      (fullBoardPartition_left_saturated e _ ht) a
    rw [fullBoardPartition_comap_left] at h
    rw [← h]
    exact hp.2 a
  | inr b =>
    have h := blockSize_comap_saturated _ hg.injective _
      (fullBoardPartition_right_saturated e _ ht) b
    rw [fullBoardPartition_comap_right] at h
    rw [← h]
    exact hq.2 b

theorem fullBoardPartition_pairBlock_left {α β γ : Type*}
    (e : γ ≃ α ⊕ β) (p : Setoid α × Setoid β) (a b : α)
    (hp : IsPairBlock p.1 a b) :
    IsPairBlock (fullBoardPartition e p) (e.symm (Sum.inl a)) (e.symm (Sum.inl b)) := by
  intro x
  obtain ⟨x,rfl⟩ := e.symm.surjective x
  cases x with
  | inl c => simpa only [fullBoardPartition_rel,Equiv.apply_symm_apply,
      Sum.liftRel_inl_inl,e.symm.injective.eq_iff,Sum.inl.injEq] using hp c
  | inr c => simp only [fullBoardPartition_rel,Equiv.apply_symm_apply,
      Sum.not_liftRel_inl_inr,e.symm.injective.eq_iff,Sum.inr_ne_inl,or_self]

end LC004

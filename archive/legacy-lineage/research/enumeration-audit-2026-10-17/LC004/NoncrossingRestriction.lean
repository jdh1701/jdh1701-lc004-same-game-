import LC004.PartitionCounting

namespace LC004

/-- The positive form of noncrossing: interleaving equivalent pairs lie in
the same equivalence class. Positions may be any linearly ordered type. -/
def IsNoncrossing {α : Type*} [LinearOrder α] (r : Setoid α) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → r a c → r b d → r a b

def restrictToBlock {α : Type*} (r s : Setoid α) (a : α) :
    Setoid {x : α // s x a} := Setoid.comap Subtype.val r

/-- Restriction to an ordered subset preserves noncrossing. -/
theorem noncrossing_restrict {α : Type*} [LinearOrder α]
    {r : Setoid α} (hr : IsNoncrossing r) (s : Setoid α) (a : α) :
    IsNoncrossing (restrictToBlock r s a) := by
  intro b c d e hbc hcd hde hbd hce
  exact hr b.val c.val d.val e.val hbc hcd hde hbd hce

/-- Below a noncrossing partition, noncrossing can be checked independently
inside its blocks. This is the geometric step used in witness factorization. -/
theorem noncrossing_iff_blocks {α : Type*} [LinearOrder α]
    (r s : Setoid α) (hrs : r ≤ s) (hs : IsNoncrossing s) :
    IsNoncrossing r ↔ ∀ a, IsNoncrossing (restrictToBlock r s a) := by
  constructor
  · intro hr a
    exact noncrossing_restrict hr s a
  · intro h a b c d hab hbc hcd hac hbd
    have sac : s a c := hrs hac
    have sbd : s b d := hrs hbd
    have sab : s a b := hs a b c d hab hbc hcd sac sbd
    have sba : s b a := s.symm sab
    have sca : s c a := s.symm sac
    have sda : s d a := s.trans (s.symm sbd) sba
    exact h a ⟨a,s.refl a⟩ ⟨b,sba⟩ ⟨c,sca⟩ ⟨d,sda⟩ hab hbc hcd hac hbd

/-- Refining a coarse partition does not split a fine block when it is viewed
inside its containing coarse block. The equivalence preserves each position. -/
def blockRestrictionEquiv {α : Type*} (r s : Setoid α) (hrs : r ≤ s) (a : α) :
    {x : α // r x a} ≃ {x : {y : α // s y a} // r x.val a} where
  toFun x := ⟨⟨x.val, hrs x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem blockRestriction_card {α : Type*} [Fintype α]
    (r s : Setoid α) (hrs : r ≤ s) (a : α) :
    @Fintype.card {x : α // r x a} (Fintype.ofFinite _) =
    @Fintype.card {x : {y : α // s y a} // r x.val a} (Fintype.ofFinite _) := by
  classical
  exact @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
    (blockRestrictionEquiv r s hrs a)

noncomputable def partitionBlockSize {α : Type*} [Finite α] (r : Setoid α) (a : α) : Nat :=
  @Fintype.card {x : α // r x a} (Fintype.ofFinite _)

/-- Each fine block retains its cardinality inside any containing coarse block. -/
theorem restrictedBlockSize {α : Type*} [Finite α]
    (r s : Setoid α) (hrs : r ≤ s) (a : α) (b : {x : α // s x a}) :
    partitionBlockSize (restrictToBlock r s a) b = partitionBlockSize r b.val := by
  classical
  apply @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
  exact {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,s.trans (hrs x.property) b.property⟩,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- A noncrossing equality partition all of whose blocks have size two or three.
Equivalence with the executable witness generator is still a separate theorem. -/
def PairTriplePartition {α : Type*} [LinearOrder α] [Finite α] (r : Setoid α) : Prop :=
  IsNoncrossing r ∧ ∀ a, partitionBlockSize r a = 2 ∨ partitionBlockSize r a = 3

/-- The complete pair/triple witness property separates over noncrossing blocks. -/
theorem pairTriple_iff_blocks {α : Type*} [LinearOrder α] [Finite α]
    (r s : Setoid α) (hrs : r ≤ s) (hs : IsNoncrossing s) :
    PairTriplePartition r ↔ ∀ a, PairTriplePartition (restrictToBlock r s a) := by
  constructor
  · rintro ⟨hn,hsize⟩ a
    refine ⟨noncrossing_restrict hn s a, ?_⟩
    intro b
    rw [restrictedBlockSize r s hrs a b]
    exact hsize b.val
  · intro h
    refine ⟨(noncrossing_iff_blocks r s hrs hs).mpr (fun a => (h a).1), ?_⟩
    intro a
    have hz := (h a).2 ⟨a,s.refl a⟩
    simpa only [restrictedBlockSize r s hrs a] using hz

#print axioms noncrossing_iff_blocks
#print axioms blockRestriction_card
#print axioms pairTriple_iff_blocks

end LC004

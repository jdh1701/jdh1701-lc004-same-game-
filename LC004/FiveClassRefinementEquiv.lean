import LC004.FiveClassLocalRefinement

namespace LC004
open scoped Classical

noncomputable def setoidClassFinset {α : Type*} [Fintype α]
    (r : Setoid α) (u : α) : Finset α := Finset.univ.filter (r u)

def SetoidSmallClasses23 {α : Type*} [Fintype α] (r : Setoid α) : Prop :=
  ∀ u, (setoidClassFinset r u).card = 2 ∨ (setoidClassFinset r u).card = 3

def fiveClassRestriction {k : Nat} (r : Setoid (Fin k × Fin 5)) (i : Fin k) :
    ColorPattern 5 := Setoid.comap (fun u => (i,u)) r

theorem fiveClassRestriction_assignment {k : Nat} (a : Fin k → Fin 10) (i : Fin k) :
    fiveClassRestriction (fiveAssignmentSetoid a) i = fiveLocalSplit (a i) := by
  apply Setoid.ext
  intro u v
  change (i,fiveSplitBit (a i) u) = (i,fiveSplitBit (a i) v) ↔ _
  simp only [Prod.mk.injEq,true_and]
  rfl

theorem fiveAssignmentSetoid_injective {k : Nat} :
    Function.Injective (@fiveAssignmentSetoid k) := by
  intro a b he
  funext i
  apply fiveLocalSplit_injective
  rw [← fiveClassRestriction_assignment a i, ← fiveClassRestriction_assignment b i]
  exact congrArg (fun r => fiveClassRestriction r i) he

/-- A refinement cannot relate points in different original classes, so local
and global class cardinalities agree exactly. -/
theorem fiveClassRestriction_class_card {k : Nat} (r : Setoid (Fin k × Fin 5))
    (hr : r ≤ fiveClassBaseSetoid k) (i : Fin k) (u : Fin 5) :
    (patternClassPositions (fiveClassRestriction r i) u).card =
      (setoidClassFinset r (i,u)).card := by
  classical
  apply Finset.card_bij (fun v _ => (i,v))
  · intro v hv
    simpa only [setoidClassFinset,patternClassPositions,Finset.mem_filter,
      Finset.mem_univ,true_and,fiveClassRestriction,Setoid.comap_rel] using hv
  · intro v _ w _ he
    exact congrArg Prod.snd he
  · rintro ⟨j,v⟩ hv
    have hrel : r (i,u) (j,v) := by simpa [setoidClassFinset] using hv
    have hij : i = j := hr hrel
    subst j
    exact ⟨v,by simpa [patternClassPositions,fiveClassRestriction,Setoid.comap_rel] using hrel,rfl⟩

/-- Every small-class refinement of an all-five partition has a unique tuple
of pair choices. No winning or noncrossing assumption is used here. -/
theorem five_small_refinement_unique_assignment {k : Nat}
    (r : Setoid (Fin k × Fin 5)) (hr : r ≤ fiveClassBaseSetoid k)
    (hsmall : SetoidSmallClasses23 r) :
    ∃! a : Fin k → Fin 10, r = fiveAssignmentSetoid a := by
  have hlocal : ∀ i : Fin k, ∃! s : Fin 10, fiveClassRestriction r i = fiveLocalSplit s := by
    intro i
    apply five_small_pattern_unique_split
    intro u
    rw [fiveClassRestriction_class_card r hr i u]
    exact hsmall (i,u)
  let a : Fin k → Fin 10 := fun i => Classical.choose (hlocal i)
  have ha : ∀ i, fiveClassRestriction r i = fiveLocalSplit (a i) :=
    fun i => (Classical.choose_spec (hlocal i)).1
  have he : r = fiveAssignmentSetoid a := by
    apply Setoid.ext
    rintro ⟨i,u⟩ ⟨j,v⟩
    by_cases hij : i = j
    · subst j
      have hh : r (i,u) (i,v) ↔ fiveSplitBit (a i) u = fiveSplitBit (a i) v := by
        change fiveClassRestriction r i u v ↔ fiveLocalSplit (a i) u v
        rw [ha i]
      change r (i,u) (i,v) ↔ (i,fiveSplitBit (a i) u) = (i,fiveSplitBit (a i) v)
      simpa only [Prod.mk.injEq,true_and] using hh
    · constructor
      · intro h
        exact (hij (hr h)).elim
      · intro h
        change (i,fiveSplitBit (a i) u) = (j,fiveSplitBit (a j) v) at h
        exact (hij (congrArg Prod.fst h)).elim
  exact ⟨a,he,fun b hb => fiveAssignmentSetoid_injective (hb.symm.trans he)⟩

theorem fiveAssignmentSetoid_small {k : Nat} (a : Fin k → Fin 10) :
    SetoidSmallClasses23 (fiveAssignmentSetoid a) := by
  rintro ⟨i,u⟩
  rw [← fiveClassRestriction_class_card _ (fiveAssignmentSetoid_le_base a) i u,
    fiveClassRestriction_assignment]
  have he : patternClassPositions (fiveLocalSplit (a i)) u =
      Finset.univ.filter (fun v => fiveSplitBit (a i) u = fiveSplitBit (a i) v) := by
    ext v
    simp [patternClassPositions,fiveLocalSplit,Setoid.ker_def]
  rw [he]
  exact fiveLocalSplit_class_sizes (a i) u

/-- A duplication-free equivalence for the complete small-refinement interval. -/
noncomputable def fiveSmallRefinementEquiv (k : Nat) :
    (Fin k → Fin 10) ≃
      {r : Setoid (Fin k × Fin 5) // r ≤ fiveClassBaseSetoid k ∧ SetoidSmallClasses23 r} :=
  Equiv.ofBijective
    (fun a => ⟨fiveAssignmentSetoid a,fiveAssignmentSetoid_le_base a,fiveAssignmentSetoid_small a⟩)
    ⟨fun a b h => fiveAssignmentSetoid_injective (congrArg Subtype.val h), by
      rintro ⟨r,hr,hs⟩
      obtain ⟨a,ha,_⟩ := five_small_refinement_unique_assignment r hr hs
      exact ⟨a,Subtype.ext ha.symm⟩⟩

#print axioms fiveSmallRefinementEquiv
end LC004

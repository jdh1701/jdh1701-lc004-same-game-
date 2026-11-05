import LC004.ChoiceBoundaryClassification

namespace LC004

/-- The canonical bipartition selected by a pair in a five-point class. -/
def fiveSplitBit (s : Fin 10) (u : Fin 5) : Bool :=
  decide (u.val ∈ fivePairRanks s)

def fiveLocalSplit (s : Fin 10) : Setoid (Fin 5) := Setoid.ker (fiveSplitBit s)

/-- Two different pair/triple splits connect every pair of class positions in
at most two steps. The finite proof checks all labels and endpoints. -/
theorem fiveLocalSplit_two_step : ∀ s t : Fin 10, s ≠ t → ∀ u v : Fin 5,
    ∃ w : Fin 5,
      (fiveSplitBit s u = fiveSplitBit s w ∨ fiveSplitBit t u = fiveSplitBit t w) ∧
      (fiveSplitBit s w = fiveSplitBit s v ∨ fiveSplitBit t w = fiveSplitBit t v) := by
  decide +kernel

theorem fiveLocalSplit_nonconstant : ∀ s : Fin 10, ∃ u v : Fin 5,
    fiveSplitBit s u ≠ fiveSplitBit s v := by decide +kernel

theorem fiveLocalSplit_class_sizes : ∀ s : Fin 10, ∀ u : Fin 5,
    (Finset.univ.filter (fun v => fiveSplitBit s u = fiveSplitBit s v)).card = 2 ∨
    (Finset.univ.filter (fun v => fiveSplitBit s u = fiveSplitBit s v)).card = 3 := by
  decide +kernel

theorem fiveLocalSplit_join_eq_top (s t : Fin 10) (hst : s ≠ t) :
    fiveLocalSplit s ⊔ fiveLocalSplit t = ⊤ := by
  apply Setoid.ext
  intro u v
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨w,huw,hwv⟩ := fiveLocalSplit_two_step s t hst u v
    have hs (x y : Fin 5) (h : fiveSplitBit s x = fiveSplitBit s y) :
        (fiveLocalSplit s ⊔ fiveLocalSplit t) x y := (Setoid.le_def.mp (show fiveLocalSplit s ≤ fiveLocalSplit s ⊔ fiveLocalSplit t from le_sup_left)) h
    have ht (x y : Fin 5) (h : fiveSplitBit t x = fiveSplitBit t y) :
        (fiveLocalSplit s ⊔ fiveLocalSplit t) x y := (Setoid.le_def.mp (show fiveLocalSplit t ≤ fiveLocalSplit s ⊔ fiveLocalSplit t from le_sup_right)) h
    apply (fiveLocalSplit s ⊔ fiveLocalSplit t).trans
    · exact huw.elim (hs u w) (ht u w)
    · exact hwv.elim (hs w v) (ht w v)

/-- A coordinate is an original class and its second component a rank within
that class. This is the canonical model before relabeling to board positions. -/
def fiveAssignmentSetoid {k : Nat} (a : Fin k → Fin 10) : Setoid (Fin k × Fin 5) :=
  Setoid.ker (fun u => (u.1, fiveSplitBit (a u.1) u.2))

def fiveClassBaseSetoid (k : Nat) : Setoid (Fin k × Fin 5) := Setoid.ker Prod.fst

theorem fiveAssignmentSetoid_le_base {k : Nat} (a : Fin k → Fin 10) :
    fiveAssignmentSetoid a ≤ fiveClassBaseSetoid k := by
  intro u v h
  change (u.1, fiveSplitBit (a u.1) u.2) = (v.1, fiveSplitBit (a v.1) v.2) at h
  change u.1 = v.1
  exact congrArg (fun z : Fin k × Bool => z.1) h

/-- Exactly the separated pairs merge every five-point class. This connects
the surviving-pair face criterion to a genuine partition join, uniformly in k. -/
theorem fiveAssignmentSetoid_join_eq_base_iff {k : Nat} (a b : Fin k → Fin 10) :
    fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b = fiveClassBaseSetoid k ↔
      ∀ i, a i ≠ b i := by
  constructor
  · intro he i hab
    let barrier : Setoid (Fin k × Fin 5) :=
      Setoid.ker (fun u => if u.1 = i then fiveSplitBit (a i) u.2 else false)
    have hle (c : Fin k → Fin 10) (hc : c i = a i) : fiveAssignmentSetoid c ≤ barrier := by
      rintro ⟨j,u⟩ ⟨l,v⟩ h
      change (j, fiveSplitBit (c j) u) = (l, fiveSplitBit (c l) v) at h
      have hjl : j = l := congrArg Prod.fst h
      subst l
      by_cases hj : j = i
      · subst j
        have hb : fiveSplitBit (c i) u = fiveSplitBit (c i) v := congrArg Prod.snd h
        simpa only [barrier,Setoid.ker_def,if_pos rfl,hc] using hb
      · simp only [barrier,Setoid.ker_def,hj,if_false]
    have hs : fiveClassBaseSetoid k ≤ barrier := by
      rw [← he]
      exact sup_le (hle a rfl) (hle b hab.symm)
    obtain ⟨u,v,huv⟩ := fiveLocalSplit_nonconstant (a i)
    have hh := hs (show fiveClassBaseSetoid k (i,u) (i,v) from rfl)
    exact huv (by simpa only [barrier,Setoid.ker_def,if_pos rfl] using hh)
  · intro hdiff
    apply le_antisymm (sup_le (fiveAssignmentSetoid_le_base a) (fiveAssignmentSetoid_le_base b))
    rintro ⟨i,u⟩ ⟨j,v⟩ h
    change i = j at h
    subst j
    obtain ⟨w,huw,hwv⟩ := fiveLocalSplit_two_step (a i) (b i) (hdiff i) u v
    have ha (x y : Fin 5) (hxy : fiveSplitBit (a i) x = fiveSplitBit (a i) y) :
        (fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b) (i,x) (i,y) := by
      have hs : fiveAssignmentSetoid a ≤ fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b := le_sup_left
      apply hs
      change (i,fiveSplitBit (a i) x) = (i,fiveSplitBit (a i) y)
      exact Prod.ext rfl hxy
    have hb (x y : Fin 5) (hxy : fiveSplitBit (b i) x = fiveSplitBit (b i) y) :
        (fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b) (i,x) (i,y) := by
      have hs : fiveAssignmentSetoid b ≤ fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b := le_sup_right
      apply hs
      change (i,fiveSplitBit (b i) x) = (i,fiveSplitBit (b i) y)
      exact Prod.ext rfl hxy
    exact (fiveAssignmentSetoid a ⊔ fiveAssignmentSetoid b).trans
      (huw.elim (ha u w) (hb u w)) (hwv.elim (ha w v) (hb w v))

#print axioms fiveLocalSplit_join_eq_top
#print axioms fiveAssignmentSetoid_join_eq_base_iff
end LC004

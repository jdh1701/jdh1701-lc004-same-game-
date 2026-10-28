import LC004.MatchingDyckInjective

namespace LC004

/-- A perfect noncrossing matching expressed by its endpoint involution.
This form supports recursive concatenation and enclosure constructions. -/
structure EndpointMatching (n : Nat) where
  mate : Fin n → Fin n
  twice : ∀ i, mate (mate i) = i
  nofixed : ∀ i, mate i ≠ i
  noCross : ∀ a b c d, a < b → b < c → c < d → mate a = c → mate b = d → False

namespace EndpointMatching

def pattern {n : Nat} (m : EndpointMatching n) : ColorPattern n where
  r i j := i = j ∨ m.mate i = j
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · rintro i j (h | h)
      · exact Or.inl h.symm
      · right
        have hh := congrArg m.mate h
        rw [m.twice] at hh
        exact hh.symm
    · rintro i j k (hij | hij) (hjk | hjk)
      · exact Or.inl (hij.trans hjk)
      · subst j
        exact Or.inr hjk
      · exact Or.inr (hij.trans hjk)
      · have hh := congrArg m.mate hij
        rw [m.twice] at hh
        exact Or.inl (hh.trans hjk)

theorem pattern_class {n : Nat} (m : EndpointMatching n) (i : Fin n) :
    patternClassPositions m.pattern i = {i, m.mate i} := by
  classical
  ext j
  simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  change (i = j ∨ m.mate i = j) ↔ (j = i ∨ j = m.mate i)
  exact ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem pattern_noncrossing {n : Nat} (m : EndpointMatching n) :
    NoncrossingPairPattern m.pattern := by
  classical
  constructor
  · intro i
    have hc : (patternClassPositions m.pattern i).card = 2 := by
      rw [m.pattern_class]
      simp [m.nofixed i, Ne.symm (m.nofixed i)]
    simpa only [patternClassPositions, Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  · rintro a b c d hab hbc hcd ⟨hac, hbd⟩
    rcases hac with h | h
    · omega
    · rcases hbd with h' | h'
      · omega
      · exact m.noCross a b c d hab hbc hcd h h'

theorem pattern_partner {n : Nat} (m : EndpointMatching n) (i : Fin n) :
    matchingPartner m.pattern m.pattern_noncrossing i = m.mate i :=
  matchingPartner_unique m.pattern m.pattern_noncrossing i (m.mate i) (m.nofixed i) (Or.inr rfl)

noncomputable def ofPattern {n : Nat} (p : ColorPattern n) (hp : NoncrossingPairPattern p) :
    EndpointMatching n where
  mate := matchingPartner p hp
  twice := matchingPartner_twice p hp
  nofixed i := (matchingPartner_spec p hp i).1
  noCross := by
    intro a b c d hab hbc hcd hac hbd
    exact hp.2 a b c d hab hbc hcd
      ⟨hac ▸ (matchingPartner_spec p hp a).2, hbd ▸ (matchingPartner_spec p hp b).2⟩

theorem fin_add_witness {n k : Nat} (x : Fin (n + k)) :
    (∃ i : Fin n, x = Fin.castAdd k i) ∨ (∃ j : Fin k, x = Fin.natAdd n j) :=
  Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) x

def appendMate {n k : Nat} (m : EndpointMatching n) (t : EndpointMatching k) :
    Fin (n + k) → Fin (n + k) :=
  Fin.addCases (fun i => Fin.castAdd k (m.mate i)) (fun j => Fin.natAdd n (t.mate j))

/-- Concatenate matchings in disjoint consecutive intervals. -/
def append {n k : Nat} (m : EndpointMatching n) (t : EndpointMatching k) : EndpointMatching (n + k) where
  mate := appendMate m t
  twice := by
    intro x
    rcases fin_add_witness x with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;>
      simp only [appendMate, Fin.addCases_left, Fin.addCases_right, m.twice, t.twice]
  nofixed := by
    intro x h
    rcases fin_add_witness x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp only [appendMate, Fin.addCases_left] at h
      exact m.nofixed i (Fin.ext (congrArg Fin.val h))
    · simp only [appendMate, Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      change n + (t.mate j).val = n + j.val at hv
      exact t.nofixed j (Fin.ext (Nat.add_left_cancel hv))
  noCross := by
    intro a b c d hab hbc hcd hac hbd
    subst c
    subst d
    rcases fin_add_witness a with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases fin_add_witness b with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp only [appendMate, Fin.addCases_left, Fin.lt_def, Fin.coe_castAdd] at hab hbc hcd
      exact m.noCross i j (m.mate i) (m.mate j) hab hbc hcd rfl rfl
    · simp only [appendMate, Fin.addCases_left, Fin.addCases_right,
        Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at hab hbc hcd
      have hb := (m.mate i).isLt
      omega
    · simp only [appendMate, Fin.addCases_left, Fin.addCases_right,
        Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at hab hbc hcd
      have hb := j.isLt
      omega
    · simp only [appendMate, Fin.addCases_right, Fin.lt_def, Fin.coe_natAdd] at hab hbc hcd
      exact t.noCross i j (t.mate i) (t.mate j) (by omega) (by omega) (by omega) rfl rfl

def interior {n : Nat} (i : Fin n) : Fin (n + 2) := i.castSucc.succ

def nestMate {n : Nat} (m : EndpointMatching n) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases (Fin.last (n + 1)) (Fin.lastCases 0 (fun i => interior (m.mate i)))

@[simp] theorem nestMate_zero {n : Nat} (m : EndpointMatching n) :
    nestMate m 0 = Fin.last (n + 1) := by simp [nestMate]

@[simp] theorem nestMate_last {n : Nat} (m : EndpointMatching n) :
    nestMate m (Fin.last (n + 1)) = 0 := by
  change nestMate m (Fin.last n).succ = 0
  simp [nestMate]

@[simp] theorem nestMate_interior {n : Nat} (m : EndpointMatching n) (i : Fin n) :
    nestMate m (interior i) = interior (m.mate i) := by simp [nestMate, interior]

theorem fin_nest_witness {n : Nat} (x : Fin (n + 2)) :
    x = 0 ∨ x = Fin.last (n + 1) ∨ ∃ i : Fin n, x = interior i := by
  refine Fin.cases (Or.inl rfl) (fun j => ?_) x
  refine Fin.lastCases (Or.inr (Or.inl rfl)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) j

/-- Enclose a matching with a new outer pair. -/
def nest {n : Nat} (m : EndpointMatching n) : EndpointMatching (n + 2) where
  mate := nestMate m
  twice := by
    intro x
    rcases fin_nest_witness x with rfl | rfl | ⟨i, rfl⟩ <;> simp [m.twice]
  nofixed := by
    intro x h
    rcases fin_nest_witness x with rfl | rfl | ⟨i, rfl⟩
    · have hv := congrArg Fin.val h
      simp only [nestMate_zero, Fin.val_last, Fin.val_zero] at hv
      omega
    · have hv := congrArg Fin.val h
      simp only [nestMate_last, Fin.val_zero, Fin.val_last] at hv
      omega
    · rw [nestMate_interior] at h
      have hv := congrArg Fin.val h
      change (m.mate i).val + 1 = i.val + 1 at hv
      exact m.nofixed i (Fin.ext (Nat.add_right_cancel hv))
  noCross := by
    intro a b c d hab hbc hcd hac hbd
    subst c
    subst d
    rcases fin_nest_witness a with rfl | rfl | ⟨i, rfl⟩
    · rw [nestMate_zero] at hcd
      have hb := (nestMate m b).isLt
      change n + 1 < (nestMate m b).val at hcd
      omega
    · have hb := b.isLt
      change n + 1 < b.val at hab
      omega
    · rcases fin_nest_witness b with rfl | rfl | ⟨j, rfl⟩
      · change i.val + 1 < 0 at hab
        omega
      · rw [nestMate_last] at hcd
        change (nestMate m (interior i)).val < 0 at hcd
        omega
      · rw [nestMate_interior] at hbc hcd
        rw [nestMate_interior] at hcd
        change i.val + 1 < j.val + 1 at hab
        change j.val + 1 < (m.mate i).val + 1 at hbc
        change (m.mate i).val + 1 < (m.mate j).val + 1 at hcd
        exact m.noCross i j (m.mate i) (m.mate j) (by omega) (by omega) (by omega) rfl rfl

#print axioms pattern_noncrossing
#print axioms append
#print axioms nest

end EndpointMatching
end LC004

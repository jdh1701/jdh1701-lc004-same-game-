import LC004.SmallPatternCorrespondence

namespace LC004

/-- The least noncrossing equivalence relation containing the input pattern.
Defined intrinsically by all noncrossing coarsenings, without choosing merges. -/
def noncrossingClosure {n : Nat} (p : ColorPattern n) : ColorPattern n where
  r a b := ∀ q : ColorPattern n, p ≤ q → PatternNoncrossing q → q a b
  iseqv := by
    constructor
    · intro a q _ _
      exact q.refl a
    · intro a b h q hp hnc
      exact q.symm (h q hp hnc)
    · intro a b c hab hbc q hp hnc
      exact q.trans (hab q hp hnc) (hbc q hp hnc)

theorem le_noncrossingClosure {n : Nat} (p : ColorPattern n) :
    p ≤ noncrossingClosure p := by
  intro a b h q hp _
  exact hp h

theorem noncrossingClosure_noncrossing {n : Nat} (p : ColorPattern n) :
    PatternNoncrossing (noncrossingClosure p) := by
  intro a b c d hab hbc hcd hac hbd q hp hnc
  exact hnc a b c d hab hbc hcd (hac q hp hnc) (hbd q hp hnc)

theorem noncrossingClosure_minimal {n : Nat} (p q : ColorPattern n)
    (hpq : p ≤ q) (hnc : PatternNoncrossing q) : noncrossingClosure p ≤ q := by
  intro a b h
  exact h q hpq hnc

theorem noncrossingClosure_le_iff {n : Nat} (p q : ColorPattern n)
    (hnc : PatternNoncrossing q) : noncrossingClosure p ≤ q ↔ p ≤ q :=
  ⟨fun h => le_trans (le_noncrossingClosure p) h,
    fun h => noncrossingClosure_minimal p q h hnc⟩

theorem noncrossingClosure_eq_self {n : Nat} (p : ColorPattern n)
    (hnc : PatternNoncrossing p) : noncrossingClosure p = p :=
  le_antisymm (noncrossingClosure_minimal p p le_rfl hnc) (le_noncrossingClosure p)

theorem noncrossingClosure_eq_self_iff {n : Nat} (p : ColorPattern n) :
    noncrossingClosure p = p ↔ PatternNoncrossing p := by
  constructor
  · intro h
    rw [← h]
    exact noncrossingClosure_noncrossing p
  · exact noncrossingClosure_eq_self p

theorem noncrossingClosure_mono {n : Nat} :
    Monotone (@noncrossingClosure n) := by
  intro p q hpq
  exact noncrossingClosure_minimal p (noncrossingClosure q)
    (le_trans hpq (le_noncrossingClosure q)) (noncrossingClosure_noncrossing q)

theorem noncrossingClosure_idempotent {n : Nat} (p : ColorPattern n) :
    noncrossingClosure (noncrossingClosure p) = noncrossingClosure p :=
  noncrossingClosure_eq_self _ (noncrossingClosure_noncrossing p)

def NCConnected {n : Nat} (p : ColorPattern n) : Prop := noncrossingClosure p = ⊤

theorem ncConnected_iff_no_proper_noncrossing_coarsening {n : Nat}
    (p : ColorPattern n) :
    NCConnected p ↔ ∀ q : ColorPattern n, p ≤ q → PatternNoncrossing q → q = ⊤ := by
  constructor
  · intro h q hp hnc
    apply top_unique
    rw [← h]
    exact noncrossingClosure_minimal p q hp hnc
  · intro h
    exact h _ (le_noncrossingClosure p) (noncrossingClosure_noncrossing p)

#print axioms noncrossingClosure_noncrossing
#print axioms noncrossingClosure_le_iff
#print axioms ncConnected_iff_no_proper_noncrossing_coarsening
end LC004

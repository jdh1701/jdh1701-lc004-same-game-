import LC004.FullBoardCancellation
import Mathlib.Tactic.FinCases

namespace LC004

open scoped Classical in
theorem partitionBlockSize_fin4 (r : Setoid (Fin 4)) (a : Fin 4) :
    partitionBlockSize r a =
      (if r 0 a then 1 else 0) + (if r 1 a then 1 else 0) +
      (if r 2 a then 1 else 0) + (if r 3 a then 1 else 0) := by
  classical
  unfold partitionBlockSize
  rw [Fintype.card_subtype]
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  rw [hu]
  by_cases h0 : r 0 a <;> by_cases h1 : r 1 a <;>
    by_cases h2 : r 2 a <;> by_cases h3 : r 3 a <;>
    simp [Finset.filter_insert,Finset.filter_singleton,h0,h1,h2,h3]

set_option maxHeartbeats 800000 in
/-- Exhaustive classification, using block sizes and noncrossing, rather
than an assumed pairing branch decomposition. -/
theorem pairTriple_fin4_classification (r : Setoid (Fin 4))
    (hr : PairTriplePartition r) : r = quadAdjacent ∨ r = quadNested := by
  classical
  have hs (i j : Fin 4) : r i j ↔ r j i := ⟨r.symm,r.symm⟩
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h30 := hs 3 0
  have h21 := hs 2 1
  have h31 := hs 3 1
  have h32 := hs 3 2
  clear hs
  have h00 : r 0 0 := r.refl 0
  have h11 : r 1 1 := r.refl 1
  have h22 : r 2 2 := r.refl 2
  have h33 : r 3 3 := r.refl 3
  have hc0 := hr.2 0
  have hc1 := hr.2 1
  have hc2 := hr.2 2
  have hc3 := hr.2 3
  simp only [partitionBlockSize_fin4,h10,h20,h30,h21,h31,h32,h00,h11,h22,h33,if_true] at hc0 hc1 hc2 hc3
  have hnc := hr.1 0 1 2 3 (by decide) (by decide) (by decide)
  have ht012 : r 0 1 → r 1 2 → r 0 2 := fun h k => r.trans h k
  have ht013 : r 0 1 → r 1 3 → r 0 3 := fun h k => r.trans h k
  have ht023 : r 0 2 → r 2 3 → r 0 3 := fun h k => r.trans h k
  have ht123 : r 1 2 → r 2 3 → r 1 3 := fun h k => r.trans h k
  have ht102 : r 0 1 → r 0 2 → r 1 2 := fun h k => r.trans (r.symm h) k
  have ht103 : r 0 1 → r 0 3 → r 1 3 := fun h k => r.trans (r.symm h) k
  have ht203 : r 0 2 → r 0 3 → r 2 3 := fun h k => r.trans (r.symm h) k
  have ht213 : r 1 2 → r 1 3 → r 2 3 := fun h k => r.trans (r.symm h) k
  have ht021 : r 0 2 → r 1 2 → r 0 1 := fun h k => r.trans h (r.symm k)
  have ht031 : r 0 3 → r 1 3 → r 0 1 := fun h k => r.trans h (r.symm k)
  have ht032 : r 0 3 → r 2 3 → r 0 2 := fun h k => r.trans h (r.symm k)
  have ht132 : r 1 3 → r 2 3 → r 1 2 := fun h k => r.trans h (r.symm k)
  clear hr
  have hclass :
      (r 0 1 ∧ ¬r 0 2 ∧ ¬r 0 3 ∧ ¬r 1 2 ∧ ¬r 1 3 ∧ r 2 3) ∨
      (¬r 0 1 ∧ ¬r 0 2 ∧ r 0 3 ∧ r 1 2 ∧ ¬r 1 3 ∧ ¬r 2 3) := by
    by_cases h01 : r 0 1 <;> by_cases h02 : r 0 2 <;>
      by_cases h03 : r 0 3 <;> by_cases h12 : r 1 2 <;>
      by_cases h13 : r 1 3 <;> by_cases h23 : r 2 3 <;> simp_all
  clear hc0 hc1 hc2 hc3 hnc ht012 ht013 ht023 ht123
    ht102 ht103 ht203 ht213 ht021 ht031 ht032 ht132
  rcases hclass with ⟨h01,h02,h03,h12,h13,h23⟩ | ⟨h01,h02,h03,h12,h13,h23⟩
  · left
    apply Setoid.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [quadAdjacent,Setoid.ker_def] <;> decide
  · right
    apply Setoid.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [quadNested,Setoid.ker_def] <;> decide

theorem quadAdjacent_pairTriple : PairTriplePartition quadAdjacent := by
  refine ⟨?_,?_⟩
  · intro a b c d hab hbc hcd hac hbd
    have ha : a = 0 := by omega
    have hb : b = 1 := by omega
    have hc : c = 2 := by omega
    have hd : d = 3 := by omega
    subst a; subst b; subst c; subst d
    exact False.elim (Nat.zero_ne_one hac)
  · intro a
    fin_cases a <;> simp [partitionBlockSize_fin4,quadAdjacent,Setoid.ker_def] <;> decide

theorem quadNested_pairTriple : PairTriplePartition quadNested := by
  refine ⟨?_,?_⟩
  · intro a b c d hab hbc hcd hac hbd
    have ha : a = 0 := by omega
    have hb : b = 1 := by omega
    have hc : c = 2 := by omega
    have hd : d = 3 := by omega
    subst a; subst b; subst c; subst d
    exact False.elim (Nat.zero_ne_one hac)
  · intro a
    fin_cases a <;> simp [partitionBlockSize_fin4,quadNested,Setoid.ker_def] <;> decide

theorem quadAdjacent_pairBlocks :
    IsPairBlock quadAdjacent 0 1 ∧ IsPairBlock quadAdjacent 2 3 := by
  constructor <;> intro i <;> fin_cases i <;>
    simp [quadAdjacent,Setoid.ker_def] <;> decide

theorem quadNested_pairBlocks :
    IsPairBlock quadNested 0 3 ∧ IsPairBlock quadNested 1 2 := by
  constructor <;> intro i <;> fin_cases i <;>
    simp [quadNested,Setoid.ker_def] <;> decide

end LC004

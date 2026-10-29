import Mathlib

namespace LC004
open scoped BigOperators

def IsFirstHeightMinimum {n : Nat} (h : Fin (n + 1) → Int) (r : Fin (n + 1)) : Prop :=
  (∀ j, r ≤ j → h r ≤ h j) ∧ (∀ j, j < r → h r < h j)

theorem existsUnique_first_height_minimum {n : Nat} (h : Fin (n + 1) → Int) :
    ∃! r, IsFirstHeightMinimum h r := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ h
    (show (Finset.univ : Finset (Fin (n + 1))).Nonempty from ⟨0, Finset.mem_univ _⟩)
  let s := (Finset.univ : Finset (Fin (n + 1))).filter (fun i => h i = h q)
  have hs : s.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  let r := s.min' hs
  have hr := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hmin : ∀ j, h r ≤ h j := by
    intro j
    rw [hr]
    exact hq j (Finset.mem_univ j)
  have hroot : IsFirstHeightMinimum h r := by
    refine ⟨fun j _ => hmin j, ?_⟩
    intro j hj
    apply lt_of_le_of_ne (hmin j)
    intro heq
    have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm.trans hr⟩
    have hle := Finset.min'_le s j hjmem
    exact (not_lt_of_ge hle) hj
  refine ⟨r, hroot, ?_⟩
  intro t ht
  rcases lt_trichotomy r t with hlt | heq | hgt
  · have h₁ := hroot.1 t (le_of_lt hlt)
    have h₂ := ht.2 r hlt
    omega
  · exact heq.symm
  · have h₁ := ht.1 r (le_of_lt hgt)
    have h₂ := hroot.2 t hgt
    omega

noncomputable def cyclicHeight {n : Nat} (f : Fin (n + 1) → Int) (cut : Nat) : Int := by
  classical
  exact ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun i => i.val < cut), f i

def rotateWeights {n : Nat} (f : Fin (n + 1) → Int) (r : Fin (n + 1))
    (i : Fin (n + 1)) : Int := f (r + i)

def RootedWeights {n : Nat} (f : Fin (n + 1) → Int) : Prop :=
  ∀ cut, cut < n + 1 → 0 ≤ cyclicHeight f cut

open scoped Classical in
theorem cyclicHeight_rotate_reindex {n : Nat} (f : Fin (n + 1) → Int)
    (r : Fin (n + 1)) (cut : Nat) :
    cyclicHeight (rotateWeights f r) cut =
      ∑ j : Fin (n + 1), if (j - r).val < cut then f j else 0 := by
  classical
  rw [cyclicHeight, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.addLeft r) _ _ ?_
  intro i
  change (if i.val < cut then f (r + i) else 0) =
    (if (r + i - r).val < cut then f (r + i) else 0)
  rw [add_sub_cancel_left]

theorem cyclicHeight_rotate_no_wrap {n : Nat} (f : Fin (n + 1) → Int)
    (r : Fin (n + 1)) (cut : Nat) (hcut : r.val + cut ≤ n + 1) :
    cyclicHeight (rotateWeights f r) cut =
      cyclicHeight f (r.val + cut) - cyclicHeight f r.val := by
  classical
  rw [cyclicHeight_rotate_reindex]
  have hterm (j : Fin (n + 1)) :
      (if (j - r).val < cut then f j else 0) =
      (if j.val < r.val + cut then f j else 0) -
        (if j.val < r.val then f j else 0) := by
    have hdiff := Fin.intCast_val_sub_eq_sub_add_ite j r
    simp only [Fin.le_iff_val_le_val] at hdiff
    have hj := j.isLt
    have hr := r.isLt
    split_ifs at hdiff ⊢ <;> omega
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, cyclicHeight, Finset.sum_filter]

open scoped Classical in
theorem cyclicHeight_rotate_wrap {n : Nat} (f : Fin (n + 1) → Int)
    (htotal : ∑ i, f i = -1) (r : Fin (n + 1)) (cut : Nat)
    (hcut : cut ≤ n + 1) (hwrap : n + 1 ≤ r.val + cut) :
    cyclicHeight (rotateWeights f r) cut =
      cyclicHeight f (r.val + cut - (n + 1)) - cyclicHeight f r.val - 1 := by
  classical
  rw [cyclicHeight_rotate_reindex]
  have hterm (j : Fin (n + 1)) :
      (if (j - r).val < cut then f j else 0) =
      f j - (if j.val < r.val then f j else 0) +
        (if j.val < r.val + cut - (n + 1) then f j else 0) := by
    have hdiff := Fin.intCast_val_sub_eq_sub_add_ite j r
    simp only [Fin.le_iff_val_le_val] at hdiff
    have hj := j.isLt
    have hr := r.isLt
    split_ifs at hdiff ⊢ <;> omega
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, htotal,
    cyclicHeight, Finset.sum_filter]
  ring

open scoped Classical in
theorem rooted_rotation_iff_first_minimum {n : Nat} (f : Fin (n + 1) → Int)
    (htotal : ∑ i, f i = -1) (r : Fin (n + 1)) :
    RootedWeights (rotateWeights f r) ↔
      IsFirstHeightMinimum (fun j => cyclicHeight f j.val) r := by
  constructor
  · intro hroot
    constructor
    · intro j hrj
      have hcut : j.val - r.val < n + 1 := by have hj := j.isLt; omega
      have h := hroot (j.val - r.val) hcut
      rw [cyclicHeight_rotate_no_wrap f r _ (by have hj := j.isLt; omega)] at h
      have heq : r.val + (j.val - r.val) = j.val := by
        change r.val ≤ j.val at hrj
        omega
      rw [heq] at h
      omega
    · intro j hjr
      let cut := n + 1 + j.val - r.val
      have hcut : cut < n + 1 := by
        change j.val < r.val at hjr
        have hr := r.isLt
        dsimp [cut]
        omega
      have h := hroot cut hcut
      have hwrap : n + 1 ≤ r.val + cut := by
        have hr := r.isLt
        dsimp [cut]
        omega
      rw [cyclicHeight_rotate_wrap f htotal r cut (by omega) hwrap] at h
      have heq : r.val + cut - (n + 1) = j.val := by
        have hr := r.isLt
        dsimp [cut]
        omega
      rw [heq] at h
      omega
  · intro hmin cut hcut
    by_cases hwrap : n + 1 ≤ r.val + cut
    · rw [cyclicHeight_rotate_wrap f htotal r cut (by omega) hwrap]
      let j : Fin (n + 1) := ⟨r.val + cut - (n + 1), by have hr := r.isLt; omega⟩
      have hjr : j < r := by change j.val < r.val; dsimp [j]; omega
      have h := hmin.2 j hjr
      change cyclicHeight f r.val < cyclicHeight f (r.val + cut - (n + 1)) at h
      omega
    · rw [cyclicHeight_rotate_no_wrap f r cut (by omega)]
      let j : Fin (n + 1) := ⟨r.val + cut, by omega⟩
      have hrj : r ≤ j := by change r.val ≤ j.val; dsimp [j]; omega
      have h := hmin.1 j hrj
      change cyclicHeight f r.val ≤ cyclicHeight f (r.val + cut) at h
      omega

open scoped Classical in
/-- The sum-minus-one cycle lemma. Integer weights are unrestricted;
there is exactly one starting index whose proper prefix sums are nonnegative. -/
theorem existsUnique_rooted_rotation {n : Nat} (f : Fin (n + 1) → Int)
    (htotal : ∑ i, f i = -1) :
    ∃! r, RootedWeights (rotateWeights f r) := by
  obtain ⟨r, hr, huniq⟩ := existsUnique_first_height_minimum (fun j => cyclicHeight f j.val)
  exact ⟨r, (rooted_rotation_iff_first_minimum f htotal r).mpr hr,
    fun s hs => huniq s ((rooted_rotation_iff_first_minimum f htotal s).mp hs)⟩

#print axioms existsUnique_rooted_rotation

end LC004

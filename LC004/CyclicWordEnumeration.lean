import LC004.CyclicRootLemma

namespace LC004
open scoped BigOperators

abbrev CyclicDegreeWord (n : Nat) := Fin (n + 1) → Fin (n + 1)

def rotateDegreeWord {n : Nat} (w : CyclicDegreeWord n) (r : Fin (n + 1)) :
    CyclicDegreeWord n := fun i => w (r + i)

def degreeWordWeights {n : Nat} (w : CyclicDegreeWord n) : Fin (n + 1) → Int :=
  fun i => (w i).val - 1

def RootedDegreeWord {n : Nat} (w : CyclicDegreeWord n) : Prop :=
  RootedWeights (degreeWordWeights w)

@[simp] theorem rotateDegreeWord_zero {n : Nat} (w : CyclicDegreeWord n) :
    rotateDegreeWord w 0 = w := by
  funext i
  simp [rotateDegreeWord]

@[simp] theorem rotateDegreeWord_add {n : Nat} (w : CyclicDegreeWord n)
    (r s : Fin (n + 1)) :
    rotateDegreeWord (rotateDegreeWord w r) s = rotateDegreeWord w (r + s) := by
  funext i
  simp only [rotateDegreeWord, add_assoc]

theorem degreeWordWeights_total {n : Nat} (w : CyclicDegreeWord n)
    (h : ∑ i, (w i).val = n) : ∑ i, degreeWordWeights w i = -1 := by
  classical
  have hc : (∑ i, ((w i).val : Int)) = (n : Int) := by exact_mod_cast h
  simp only [degreeWordWeights, Finset.sum_sub_distrib, hc, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  omega

theorem existsUnique_rooted_degree_rotation {n : Nat} (w : CyclicDegreeWord n)
    (h : ∑ i, (w i).val = n) :
    ∃! r, RootedDegreeWord (rotateDegreeWord w r) := by
  exact existsUnique_rooted_rotation (degreeWordWeights w) (degreeWordWeights_total w h)

noncomputable def degreeWordRoot {n : Nat} (w : CyclicDegreeWord n)
    (h : ∑ i, (w i).val = n) : Fin (n + 1) :=
  Classical.choose (existsUnique_rooted_degree_rotation w h)

theorem degreeWordRoot_spec {n : Nat} (w : CyclicDegreeWord n)
    (h : ∑ i, (w i).val = n) :
    RootedDegreeWord (rotateDegreeWord w (degreeWordRoot w h)) :=
  (Classical.choose_spec (existsUnique_rooted_degree_rotation w h)).1

theorem degreeWordRoot_eq {n : Nat} (w : CyclicDegreeWord n)
    (h : ∑ i, (w i).val = n) (r : Fin (n + 1))
    (hr : RootedDegreeWord (rotateDegreeWord w r)) : degreeWordRoot w h = r :=
  ((Classical.choose_spec (existsUnique_rooted_degree_rotation w h)).2 r hr).symm

/-- Cutting a rooted word at a marked occurrence is equivalent to an arbitrary
word with that occurrence at position zero. The inverse uses the unique root. -/
noncomputable def markedRootedWordEquiv {n : Nat}
    (P : CyclicDegreeWord n → Prop)
    (htotal : ∀ w, P w → ∑ i, (w i).val = n)
    (hrotate : ∀ w r, P (rotateDegreeWord w r) ↔ P w) (a : Nat) :
    (Σ w : {w : CyclicDegreeWord n // P w ∧ RootedDegreeWord w},
      {i : Fin (n + 1) // (w.val i).val = a}) ≃
    {w : CyclicDegreeWord n // P w ∧ (w 0).val = a} where
  toFun x := ⟨rotateDegreeWord x.1.val x.2.val,
    (hrotate _ _).mpr x.1.property.1, by
      simpa only [rotateDegreeWord, add_zero] using x.2.property⟩
  invFun w :=
    let r := degreeWordRoot w.val (htotal w.val w.property.1)
    ⟨⟨rotateDegreeWord w.val r, (hrotate _ _).mpr w.property.1,
      degreeWordRoot_spec w.val (htotal w.val w.property.1)⟩,
      ⟨-r, by simpa only [rotateDegreeWord, add_neg_cancel] using w.property.2⟩⟩
  left_inv x := by
    classical
    rcases x with ⟨⟨w, hw, hroot⟩, ⟨i, hi⟩⟩
    have heq : degreeWordRoot (rotateDegreeWord w i)
        (htotal _ ((hrotate w i).mpr hw)) = -i := by
      apply degreeWordRoot_eq
      simpa only [rotateDegreeWord_add, add_neg_cancel, rotateDegreeWord_zero] using hroot
    dsimp only
    rw [heq]
    simp only [rotateDegreeWord_add, add_neg_cancel, rotateDegreeWord_zero, neg_neg]
  right_inv w := by
    apply Subtype.ext
    change rotateDegreeWord (rotateDegreeWord w.val _) (-_) = w.val
    simp only [rotateDegreeWord_add, add_neg_cancel, rotateDegreeWord_zero]

open scoped Classical in
theorem marked_rooted_word_card {n : Nat}
    (P : CyclicDegreeWord n → Prop)
    (htotal : ∀ w, P w → ∑ i, (w i).val = n)
    (hrotate : ∀ w r, P (rotateDegreeWord w r) ↔ P w)
    (a m : Nat) (hcount : ∀ w, P w →
      Fintype.card {i : Fin (n + 1) // (w i).val = a} = m) :
    Fintype.card {w : CyclicDegreeWord n // P w ∧ (w 0).val = a} =
      m * Fintype.card {w : CyclicDegreeWord n // P w ∧ RootedDegreeWord w} := by
  classical
  rw [← Fintype.card_congr (markedRootedWordEquiv P htotal hrotate a), Fintype.card_sigma]
  calc
    _ = ∑ _w : {w : CyclicDegreeWord n // P w ∧ RootedDegreeWord w}, m := by
      apply Finset.sum_congr rfl
      intro w _
      exact hcount w.val w.property.1
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_comm]

#print axioms marked_rooted_word_card

end LC004

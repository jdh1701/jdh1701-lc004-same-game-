import LC004.JoinRigidBlocks
import LC004.CrossedFourCancellation

namespace LC004
open scoped Classical

/-- Own attempt (Claude, 2026-10-30): package `join_small_class_no_cross` (R2)
as a clean corollary stated in terms of an ordinary crossing `a < b < c < d`,
`x a c`, `x b d`, `¬ x a b`, rather than R2's own raw interior/exterior
hypothesis shape. R2 itself only concludes `False` from a specific witness
`u,v,w,z`; this shows that witness is always available from any genuine
crossing, so a class crossed inside a join of pair/triple certificates can
never have size <= 3. This alone says nothing about size exactly 4 (that is
geometrically possible); see `winningJoinCoefficient_ne_zero_crossed_class_card_ge_five`
below for the size-4 elimination, which needs an extra coefficient hypothesis. -/
theorem join_crossed_class_card_ge_four {n : Nat} {F : Finset (ColorPattern n)}
    {x : ColorPattern n} (hF : ∀ c ∈ F, CertificateConstraint c)
    (hle : ∀ c ∈ F, c ≤ x)
    (hmin : ∀ y : ColorPattern n, (∀ c ∈ F, c ≤ y) → x ≤ y)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : x a c) (hbd : x b d) (hnab : ¬ x a b) :
    4 ≤ (patternClassPositions x a).card := by
  by_contra hcard
  push_neg at hcard
  have hsmall : (patternClassPositions x a).card ≤ 3 := by omega
  -- `¬ x a d` follows from `¬ x a b` and `x b d` alone, with no case split:
  -- if `x a d` held, transitivity with `x b d` would force `x a b`.
  have hnad : ¬ x a d := fun had => hnab (x.symm' (x.trans' hbd (x.symm' had)))
  have hac' : a < c := hab.trans hbc
  have hz : ¬ (a < d ∧ d < c) := fun h => absurd h.2 (not_lt.mpr hcd.le)
  exact join_small_class_no_cross hF hle hmin hac' hac hsmall hbd hab hbc hz hnad

/-- Own attempt, continued: assemble the size-4 half too. A size-4 crossed
class is geometrically possible (it is NOT ruled out the way size <= 3 is by
R2), but `winningJoinCoefficient_crossed_four_zero` shows it forces the
collected coefficient to 0. Combined with `join_crossed_class_card_ge_four`,
a crossed class in a join with a NONZERO coefficient must have size >= 5.
The real content beyond gluing is producing the crossed class's own sorted
four elements from nothing but "two of its members are `a`,`c`" -- done here
via `Finset.orderEmbOfFin` (the increasing bijection `Fin 4 ↪o Fin n` onto a
card-4 Finset), matching the existing project idiom (`S.orderEmbOfFin rfl`
in `FourGapCoefficientSupport.lean`). -/
theorem winningJoinCoefficient_ne_zero_crossed_class_card_ge_five
    {n : Nat} {F : Finset (ColorPattern n)} {x : ColorPattern n}
    (hF : ∀ c ∈ F, CertificateConstraint c) (hle : ∀ c ∈ F, c ≤ x)
    (hmin : ∀ y : ColorPattern n, (∀ c ∈ F, c ≤ y) → x ≤ y)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : x a c) (hbd : x b d) (hnab : ¬ x a b)
    (hne : winningJoinCoefficient n x ≠ 0) :
    5 ≤ (patternClassPositions x a).card := by
  have h4 := join_crossed_class_card_ge_four hF hle hmin hab hbc hcd hac hbd hnab
  by_contra h5
  push_neg at h5
  have hcard4 : (patternClassPositions x a).card = 4 := by omega
  set S := patternClassPositions x a with hSdef
  set e := S.orderEmbOfFin hcard4 with hedef
  set s0 := e 0; set s1 := e 1; set s2 := e 2; set s3 := e 3
  have hs01 : s0 < s1 := e.strictMono (by decide)
  have hs12 : s1 < s2 := e.strictMono (by decide)
  have hs23 : s2 < s3 := e.strictMono (by decide)
  have hmemS : ∀ i : Fin 4, e i ∈ S := fun i => S.orderEmbOfFin_mem hcard4 i
  have hmem : ∀ z ∈ S, z = s0 ∨ z = s1 ∨ z = s2 ∨ z = s3 := by
    intro z hz
    have hzr : z ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin S hcard4]; exact hz
    obtain ⟨i, hi⟩ := hzr
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr (Or.inl hi.symm))
    · exact Or.inr (Or.inr (Or.inr hi.symm))
  have hclassEq : S = ({s0, s1, s2, s3} : Finset (Fin n)) := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hmem z, fun hz => by
      rcases hz with rfl | rfl | rfl | rfl
      · exact hmemS 0
      · exact hmemS 1
      · exact hmemS 2
      · exact hmemS 3⟩
  -- ¬ x s0 b: if s0 were related to b, transitivity through a (both in S,
  -- hence related to s0) would force x a b, contradicting hnab.
  have hs0a : x s0 a := by
    have h0 := hmemS 0
    simp only [hSdef, patternClassPositions, Finset.mem_filter, Finset.mem_univ,
      true_and] at h0
    exact x.symm' h0
  have hnotb : ¬ x s0 b := fun h => hnab (x.trans' (x.symm' hs0a) h)
  -- `winningJoinCoefficient_crossed_four_zero` wants the class listed at its
  -- own representative `s0`, not at `a`; same class (`hs0a` relates them),
  -- so transport the equality across.
  have hS0eq : patternClassPositions x s0 = patternClassPositions x a := by
    apply Finset.ext
    intro z
    simp only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => x.trans' (x.symm' hs0a) hz, fun hz => x.trans' hs0a hz⟩
  have hclassEqS0 : patternClassPositions x s0 = ({s0, s1, s2, s3} : Finset (Fin n)) := by
    rw [hS0eq, ← hSdef]; exact hclassEq
  exact hne (winningJoinCoefficient_crossed_four_zero x hs01 hs12 hs23 hclassEqS0
    hs0a (x.trans' hs0a hac) hbd hnotb (Or.inl ⟨hab, hbc, hcd⟩))

#print axioms join_crossed_class_card_ge_four
#print axioms winningJoinCoefficient_ne_zero_crossed_class_card_ge_five
end LC004

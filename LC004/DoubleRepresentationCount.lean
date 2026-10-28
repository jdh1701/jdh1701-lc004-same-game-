import Mathlib

namespace LC004
open scoped BigOperators

/-- If every object has one or two representations, the number of
representations is the number of objects plus the number represented
twice. Surjectivity and the fiber bound are explicit obligations. -/
theorem finite_one_or_two_fiber_count {R W : Type*}
    [Fintype R] [Fintype W] [DecidableEq W]
    (f : R → W) (hsurj : Function.Surjective f)
    (hbound : ∀ w, ((Finset.univ : Finset R).filter (fun r => f r = w)).card ≤ 2) :
    Fintype.card W +
      ((Finset.univ : Finset W).filter (fun w =>
        ((Finset.univ : Finset R).filter (fun r => f r = w)).card = 2)).card =
      Fintype.card R := by
  classical
  let multiplicity := fun w =>
    ((Finset.univ : Finset R).filter (fun r => f r = w)).card
  have hpos (w : W) : 0 < multiplicity w := by
    obtain ⟨r, hr⟩ := hsurj w
    exact Finset.card_pos.mpr ⟨r, by simp [hr]⟩
  have hterm (w : W) : multiplicity w = 1 + (if multiplicity w = 2 then 1 else 0) := by
    have hp := hpos w
    have hb := hbound w
    change multiplicity w ≤ 2 at hb
    split_ifs <;> omega
  have hsum : Fintype.card R = ∑ w : W, multiplicity w := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise
        (f := f) (s := (Finset.univ : Finset R)) (t := (Finset.univ : Finset W))
        (fun r _ => Finset.mem_univ (f r)))
  change Fintype.card W +
    ((Finset.univ : Finset W).filter (fun w => multiplicity w = 2)).card = _
  calc
    _ = ∑ w : W, (1 + (if multiplicity w = 2 then 1 else 0)) := by
      simp [Finset.sum_add_distrib, Finset.card_filter]
    _ = ∑ w : W, multiplicity w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact (hterm w).symm
    _ = _ := hsum.symm

theorem finite_one_or_two_fiber_subtraction {R W : Type*}
    [Fintype R] [Fintype W] [DecidableEq W]
    (f : R → W) (hsurj : Function.Surjective f)
    (hbound : ∀ w, ((Finset.univ : Finset R).filter (fun r => f r = w)).card ≤ 2) :
    Fintype.card W = Fintype.card R -
      ((Finset.univ : Finset W).filter (fun w =>
        ((Finset.univ : Finset R).filter (fun r => f r = w)).card = 2)).card := by
  have h := finite_one_or_two_fiber_count f hsurj hbound
  omega

#print axioms finite_one_or_two_fiber_count

end LC004

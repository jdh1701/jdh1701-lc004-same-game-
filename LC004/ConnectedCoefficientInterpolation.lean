import LC004.ConnectedCoefficientSupport
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace LC004
open scoped BigOperators Classical

theorem connectedGamePolynomial_constant_zero (n : Nat) (hn : 0 < n) :
    (connectedGamePolynomial n).coeff 0 = 0 := by
  rw [connectedGamePolynomial_coeff]
  unfold connectedClassCoefficient
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with h
  · have hpos : 0 < Fintype.card (Quotient p.val) :=
      Fintype.card_pos_iff.mpr ⟨Quotient.mk p.val ⟨0,hn⟩⟩
    rw [Nat.card_eq_fintype_card] at h
    omega
  · rfl

theorem connectedGameWeight_quadratic (n : Nat) (hn : 0 < n) (hsize : n < 15)
    (b : Int) : connectedGameWeight b n =
    (connectedGamePolynomial n).coeff 1 * b +
    (connectedGamePolynomial n).coeff 2 * b ^ 2 := by
  have hd : (connectedGamePolynomial n).natDegree < 3 := by
    have := connectedGamePolynomial_natDegree_le n
    omega
  rw [← connectedGamePolynomial_eval, Polynomial.eval_eq_sum_range' hd]
  simp [Finset.sum_range_succ,connectedGamePolynomial_constant_zero n hn]

/-- Exact alphabet interpolation below the first possible cubic contribution. -/
theorem connectedGameWeight_binary_interpolation (n : Nat) (hn : 0 < n)
    (hsize : n < 15) (b : Int) :
    2 * connectedGameWeight b n =
      2 * b * (2-b) * connectedGameWeight 1 n +
      b * (b-1) * connectedGameWeight 2 n := by
  rw [connectedGameWeight_quadratic n hn hsize b,
    connectedGameWeight_quadratic n hn hsize 1,
    connectedGameWeight_quadratic n hn hsize 2]
  ring

theorem connectedGameWeight_ternary_below_fifteen (n : Nat) (hn : 0 < n)
    (hsize : n < 15) : connectedGameWeight 3 n =
      3 * connectedGameWeight 2 n - 3 * connectedGameWeight 1 n := by
  have := connectedGameWeight_binary_interpolation n hn hsize 3
  omega

/-- Through degree three, the precise missing datum is the class-count-three
coefficient. This does not assume its value or supply its enumeration. -/
theorem connectedGameWeight_ternary_cubic_correction (n : Nat) (hn : 0 < n)
    (hsize : n < 20) : connectedGameWeight 3 n =
      3 * connectedGameWeight 2 n - 3 * connectedGameWeight 1 n +
      6 * connectedClassCoefficient n 3 := by
  have hd : (connectedGamePolynomial n).natDegree < 4 := by
    have := connectedGamePolynomial_natDegree_le n
    omega
  have hev (b : Int) : connectedGameWeight b n =
      (connectedGamePolynomial n).coeff 1 * b +
      (connectedGamePolynomial n).coeff 2 * b ^ 2 +
      (connectedGamePolynomial n).coeff 3 * b ^ 3 := by
    rw [← connectedGamePolynomial_eval, Polynomial.eval_eq_sum_range' hd]
    simp [Finset.sum_range_succ,connectedGamePolynomial_constant_zero n hn]
  rw [hev 3,hev 2,hev 1,← connectedGamePolynomial_coeff]
  ring

#print axioms connectedGameWeight_binary_interpolation
#print axioms connectedGameWeight_ternary_below_fifteen
#print axioms connectedGameWeight_ternary_cubic_correction
end LC004

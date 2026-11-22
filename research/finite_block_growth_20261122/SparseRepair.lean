import FiniteBlock
namespace LC004.RawGrowth

/-- At each requested scale there need only be one length. Up to d bits of
word-count loss and up to d suffix symbols can both be absorbed if n/d is
unbounded. All counts are of distinct original ternary words. -/
theorem full_of_sparse_repairs
    (cover : ∀ m : ℕ, ∃ n k d : ℕ, k+2 ≤ d ∧ m*d ≤ n ∧
      3^n ≤ 2^d * Nat.card (Short n k)) : FullTernaryGrowth := by
  apply full_iff_finite_blocks.mpr
  intro r hr hr3
  let x := r/3
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := by dsimp [x]; linarith
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ)<1/6) hx1
  obtain ⟨n,k,d,hk,hn,hc⟩ := cover m
  have power : x^n ≤ (1/6:ℝ)^d := calc
    x^n ≤ x^(m*d) := pow_le_pow_of_le_one hx.le hx1.le hn
    _ = (x^m)^d := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hm.le _
  have hweight : (2:ℝ)^d * r^(k+2) ≤ 6^d := calc
    _ ≤ (2:ℝ)^d * (3:ℝ)^d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (pow_le_pow_right₀ hr.le hk).trans (pow_le_pow_left₀ (by linarith) hr3.le d)
    _ = _ := by rw [← mul_pow]; norm_num
  have bound : (2:ℝ)^d * r^(n+(k+2)) ≤ 3^n := by
    have h := mul_le_mul power hweight (by positivity) (by positivity)
    dsimp [x] at h
    rw [div_pow,one_div,inv_pow,inv_mul_cancel₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, div_le_one (by positivity)] at h
    rw [pow_add]
    convert h using 1; ring
  have hc' : (3:ℝ)^n ≤ 2^d * Nat.card (Short n k) := by exact_mod_cast hc
  have rate := (le_of_mul_le_mul_left (bound.trans hc') (by positivity : (0:ℝ)<2^d))
  refine ⟨n+(k+2),by omega,rate.trans ?_⟩
  exact_mod_cast short_count_le_winning n k

#print axioms full_of_sparse_repairs
end LC004.RawGrowth

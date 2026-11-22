import RawGrowth
namespace LC004.RawGrowth
open Filter
open scoped Topology
private theorem lowerRate (r c L : ℝ) (hr : 0 < r) (hc : 0 < c) (hL : L < r) (k : ℕ)
  (short : ∀ᶠ n : ℕ in atTop, c*r^n ≤ Nat.card (Short n k)) :
  ∀ᶠ n : ℕ in atTop, L < (labeledWinningCount 3 n : ℝ) ^ (1/(n:ℝ)) := by
  let d := c / (r:ℝ)^(k+2)
  have hd : 0 < d := by dsimp [d]; positivity
  have freq : ∀ᶠ n : ℕ in atTop, d * (r:ℝ)^n ≤ labeledWinningCount 3 n := by
    obtain ⟨N,hN⟩ := eventually_atTop.1 short
    apply eventually_atTop.2
    refine ⟨N+(k+2),?_⟩
    intro n hn
    let m := n-(k+2)
    have h1 : N ≤ m := by dsimp [m]; omega
    have h2 : n = m+(k+2) := by dsimp [m]; omega
    have hs := hN m h1
    have hw : (Nat.card (Short m k) : ℝ) ≤ labeledWinningCount 3 (m+(k+2)) := by
      exact_mod_cast short_count_le_winning m k
    rw [h2,pow_add]
    calc
      d * ((r:ℝ)^m * r^(k+2)) = c*r^m := by dsimp [d]; field_simp [ne_of_gt hr]; ring
      _ ≤ _ := le_trans hs hw
  have hlim : Tendsto (fun n : ℕ => d ^ (1/(n:ℝ)) * r) atTop (𝓝 r) := by
    have h := (tendsto_const_nhds (x:=d)).rpow tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl hd.ne')
    simpa using h.mul (tendsto_const_nhds (x:=(r:ℝ)))
  have low := hlim.eventually (lt_mem_nhds hL)
  filter_upwards [low,freq,eventually_ne_atTop 0] with n low hn hn0
  apply lt_of_lt_of_le low
  have h := Real.rpow_le_rpow (by positivity) hn (by positivity : 0 ≤ 1/(n:ℝ))
  simpa [Real.mul_rpow hd.le (by positivity : 0 ≤ r^n),one_div,
    Real.pow_rpow_inv_natCast hr.le hn0] using h

theorem full_of_adaptive_rates
    (cover : ∀ r : ℝ, 0 < r → r < 3 → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧
       ∀ᶠ n : ℕ in atTop, c*r^n ≤ Nat.card (Short n k)) : FullTernaryGrowth := by
  apply tendsto_order.2
  constructor
  · intro L hL
    obtain ⟨r,hr,hr3⟩ := exists_between (max_lt hL (by norm_num : (0:ℝ)<3))
    obtain ⟨k,c,hc,h⟩ := cover r (lt_of_le_of_lt (le_max_right _ _) hr) hr3
    exact lowerRate r c L (lt_of_le_of_lt (le_max_right _ _) hr) hc
      (lt_of_le_of_lt (le_max_left _ _) hr) k h
  · intro U hU
    filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    have h : (labeledWinningCount 3 n : ℝ) ≤ (3:ℝ)^n := by exact_mod_cast winning_count_upper n
    have b := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1/(n:ℝ))
    apply lt_of_le_of_lt _ hU
    simpa [one_div,Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 3) hn] using b

/-- Every accepting continuation spends at least one input per pending letter. -/
theorem height_budget {q : ℕ} {s w t : List (Fin q)} (h : FusionEval s w t) :
    s.length ≤ w.length + t.length := by
  induction h <;> simp_all <;> omega

/-- The exact quotient for continuations of at most H letters. Two prefixes
can be merged exactly when their reachable supports agree up to height H. -/
theorem bounded_continuation_iff {q : ℕ} (u v : List (Fin q)) (H : ℕ) :
    (∀ w : List (Fin q), w.length ≤ H →
      (RawMaxErases (u ++ w) [] ↔ RawMaxErases (v ++ w) [])) ↔
    ∀ s : List (Fin q), s.length ≤ H →
      (s ∈ fusionReach [] u ↔ s ∈ fusionReach [] v) := by
  constructor
  · intro tests s hs
    by_cases hp : FusionProper s
    · simpa only [raw_max_win_append_proper_iff u s hp,
        raw_max_win_append_proper_iff v s hp] using tests s hs
    · exact ⟨fun h => (hp (fusionReach_proper h)).elim,
        fun h => (hp (fusionReach_proper h)).elim⟩
  · intro supp w hw
    rw [raw_max_win_append_iff_fusion_stack, raw_max_win_append_iff_fusion_stack]
    have bound (s) (hs : FusionEval s w []) : s.length ≤ H :=
      le_trans (by simpa using height_budget hs) hw
    exact ⟨fun ⟨s,hs,h⟩ => ⟨s,(supp s (bound s h)).mp hs,h⟩,
      fun ⟨s,hs,h⟩ => ⟨s,(supp s (bound s h)).mpr hs,h⟩⟩

#print axioms bounded_continuation_iff
#print axioms full_of_adaptive_rates
end LC004.RawGrowth

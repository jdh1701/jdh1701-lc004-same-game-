import LC004.FusionStack
import LC004.LabeledJoinEnumeration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LC004.RawGrowth
open Filter
open scoped Topology

/-- The main target uses the public count defined by maximal-run deletion. -/
def FullTernaryGrowth : Prop :=
  Tendsto (fun n : ℕ => (labeledWinningCount 3 n : ℝ) ^ (1/(n:ℝ))) atTop (𝓝 3)

def Short (n k : ℕ) := {f : Fin n → Fin 3 //
  ∃ s, FusionEval [] (List.ofFn f) s ∧ s.length ≤ k}

theorem clearStack (s : List (Fin 3)) : FusionEval s s [] := by
  induction s with
  | nil => exact .done []
  | cons a s ih => exact .pop a ih

private theorem fill (a : Fin 3) (k : ℕ) :
    FusionEval [] (List.replicate (k+2) a) [] := by
  have aux (j : ℕ) : FusionEval [a] (List.replicate (j+1) a) [] := by
    induction j with
    | zero => exact .pop a (.done [])
    | succ j ih => exact .stay a ih
  exact .push a (by simp) (aux k)

theorem repair (n k : ℕ) (f : Short n k) :
    ∃ u : Fin (k+2) → Fin 3, RawMaxErases (List.ofFn (Fin.append f.val u)) [] := by
  rcases f.property with ⟨s,h,hs⟩
  let tail := s ++ List.replicate ((k-s.length)+2) (0 : Fin 3)
  have len : tail.length = k+2 := by simp [tail]; omega
  have hv : ∃ u : Fin (k+2) → Fin 3, List.ofFn u = tail := by
    generalize k+2 = N at len ⊢
    subst N
    exact ⟨tail.get,List.ofFn_get _⟩
  obtain ⟨u,hu⟩ := hv
  use u
  rw [List.ofFn_fin_append,hu,raw_max_win_iff_fusionEval]
  exact fusionEval_append h (fusionEval_append (clearStack s) (fill 0 _))

/-- Counts distinct length-n words admitting a short residual, once per input.
The suffix includes at least two filler letters so every target length is fixed. -/
theorem short_count_le_winning (n k : ℕ) :
    Nat.card (Short n k) ≤ labeledWinningCount 3 (n+(k+2)) := by
  classical
  let F (f : Short n k) : {w : Fin (n+(k+2)) → Fin 3 //
       RawMaxErases (List.ofFn w) []} :=
    ⟨Fin.append f.val (repair n k f).choose, (repair n k f).choose_spec⟩
  apply Nat.card_le_card_of_injective F
  intro a b eq
  apply Subtype.ext
  funext i
  have h := congrArg (fun t => t.val (Fin.castAdd (k+2) i)) eq
  simpa [F,Fin.append_left] using h

theorem winning_count_upper (n : ℕ) : labeledWinningCount 3 n ≤ 3^n := by
  classical
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : {f : Fin n → Fin 3 // RawMaxErases (List.ofFn f) []} → _)
    Subtype.val_injective
  simpa [labeledWinningCount,Nat.card_fun] using hh

/-- A uniform positive fraction of short, repairable inputs suffices.
The fraction is measured among the original ternary words. -/
theorem full_of_short_fraction (k : ℕ) (c : ℝ) (hc : 0 < c)
    (short : ∀ᶠ n : ℕ in atTop, c * (3:ℝ)^n ≤ Nat.card (Short n k)) :
    FullTernaryGrowth := by
  let d := c / (3:ℝ)^(k+2)
  have hd : 0 < d := by dsimp [d]; positivity
  have freq : ∀ᶠ n : ℕ in atTop, d * (3:ℝ)^n ≤ labeledWinningCount 3 n := by
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
      d * ((3:ℝ)^m * 3^(k+2)) = c*3^m := by dsimp [d]; field_simp; ring
      _ ≤ _ := le_trans hs hw
  have hlim : Tendsto (fun n : ℕ => d ^ (1/(n:ℝ)) * 3) atTop (𝓝 3) := by
    have h := (tendsto_const_nhds (x:=d)).rpow tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl hd.ne')
    simpa using h.mul (tendsto_const_nhds (x:=(3:ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [freq,eventually_ne_atTop 0] with n hn hn0
    have h := Real.rpow_le_rpow (by positivity) hn (by positivity : 0 ≤ 1/(n:ℝ))
    simpa [Real.mul_rpow hd.le (by positivity : 0 ≤ (3:ℝ)^n),one_div,
      Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 3) hn0] using h
  · filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    have h : (labeledWinningCount 3 n : ℝ) ≤ (3:ℝ)^n := by
      exact_mod_cast winning_count_upper n
    have h' := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1/(n:ℝ))
    simpa [one_div,Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 3) hn] using h'

#print axioms full_of_short_fraction
#print axioms short_count_le_winning
#print axioms winning_count_upper
end LC004.RawGrowth

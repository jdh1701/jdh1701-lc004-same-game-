import AdaptiveRates
namespace LC004.RawGrowth
open Filter
open scoped Topology
private abbrev Win (q n : ℕ) :=
  {f : Fin n → Fin q // RawMaxErases (List.ofFn f) []}

/-- Each ordered pair yields a distinct raw winner, even at a monochromatic join. -/
theorem block_product (q m n : ℕ) :
    labeledWinningCount q m * labeledWinningCount q n ≤ labeledWinningCount q (m+n) := by
  let F (p : Win q m × Win q n) : Win q (m+n) :=
    ⟨Fin.append p.1.val p.2.val, by
      rw [List.ofFn_fin_append,raw_max_win_iff_fusionEval]
      exact fusionEval_append ((raw_max_win_iff_fusionEval _).mp p.1.property)
        ((raw_max_win_iff_fusionEval _).mp p.2.property)⟩
  change Nat.card (Win q m) * Nat.card (Win q n) ≤ Nat.card (Win q (m+n))
  rw [← Nat.card_prod]
  apply Nat.card_le_card_of_injective F
  intro p t h
  apply Prod.ext <;> apply Subtype.ext <;> funext i
  · simpa [F,Fin.append_left] using congrArg (fun w => w.val (Fin.castAdd n i)) h
  · simpa [F,Fin.append_right] using congrArg (fun w => w.val (Fin.natAdd m i)) h

private theorem short_zero (n : ℕ) :
    Nat.card (Short n 0) = labeledWinningCount 3 n := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  constructor
  · rintro ⟨s,h,hs⟩
    have e : s = [] := List.length_eq_zero_iff.mp (by omega)
    exact (raw_max_win_iff_fusionEval _).mpr (e ▸ h)
  · intro h
    exact ⟨[],(raw_max_win_iff_fusionEval _).mp h,by simp⟩

private theorem block_positive (n : ℕ) (hn : 2 ≤ n) : 1 ≤ labeledWinningCount 3 n := by
  let f : Short 0 (n-2) := ⟨Fin.elim0,[],by simpa using (FusionEval.done ([] : List (Fin 3))),by simp⟩
  have hh := short_count_le_winning 0 (n-2)
  letI : Finite (Short 0 (n-2)) := Finite.of_injective Subtype.val Subtype.val_injective
  have hpos := Nat.card_pos_iff.mpr (And.intro (Nonempty.intro f) (inferInstance : Finite (Short 0 (n-2))))
  have eq : 0+(n-2+2) = n := by omega
  rw [eq] at hh
  omega

theorem finite_block_lower (r : ℝ) (hr : 1 ≤ r) (k : ℕ) (hk : 0 < k)
    (cert : r^k ≤ labeledWinningCount 3 k) (n : ℕ) (hn : 2 ≤ n) :
    r^n ≤ r^(k+1) * labeledWinningCount 3 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ k+1
    · exact (pow_le_pow_right₀ hr small).trans (le_mul_of_one_le_right (by positivity)
        (by exact_mod_cast block_positive n hn))
    · let m := n-k
      have hm : m < n := by dsimp [m]; omega
      have hm2 : 2 ≤ m := by dsimp [m]; omega
      have he : n = m+k := by dsimp [m]; omega
      have lower := mul_le_mul (ih m hm hm2) cert (by positivity) (by positivity)
      have prod : (labeledWinningCount 3 m : ℝ) * labeledWinningCount 3 k ≤
        labeledWinningCount 3 (m+k) := by exact_mod_cast block_product 3 m k
      rw [he,pow_add]
      exact lower.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left prod (by positivity))

theorem full_iff_finite_blocks : FullTernaryGrowth ↔
    ∀ r : ℝ, 1 < r → r < 3 → ∃ k : ℕ, 0 < k ∧ r^k ≤ labeledWinningCount 3 k := by
  constructor
  · intro full r hr hr3
    have h := full.eventually (lt_mem_nhds hr3)
    obtain ⟨k,hk,hpos⟩ := (h.and (eventually_gt_atTop (0:ℕ))).exists
    refine ⟨k,hpos,?_⟩
    change r < (labeledWinningCount 3 k : ℝ) ^ (1/(k:ℝ)) at hk
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ r) hk.le k
    rw [← Real.rpow_mul_natCast (by positivity),one_div,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne'),Real.rpow_one] at hh
    exact hh
  · intro blocks
    apply full_of_adaptive_rates
    intro r hr hr3
    let t := max r 2
    have ht : 1 < t := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_right _ _)
    obtain ⟨k,hk,cert⟩ := blocks t ht (max_lt hr3 (by norm_num))
    refine ⟨0,1/t^(k+1),by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    rw [short_zero,one_div,← div_eq_inv_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact (pow_le_pow_left₀ hr.le (le_max_left _ _) n).trans (finite_block_lower t ht.le k hk cert n hn)

/-- If the first input differs from the current top, a proper input forces
a push on every letter. -/
private theorem proper_push_length {q : ℕ} (w : List (Fin q)) (hp : FusionProper w)
    (s t : List (Fin q)) (hd : ∀ a ∈ w.head?, s.head? ≠ some a)
    (run : FusionEval s w t) : t.length = s.length + w.length := by
  induction w generalizing s with
  | nil => cases run; simp
  | cons a w ih =>
    cases run with
    | push _ _ tail =>
      have edge : ∀ b ∈ w.head?, (a :: s).head? ≠ some b := by
        intro b hb eq
        have e : a = b := by simpa using eq
        subst b
        exact hp.1 hb
      have h := ih hp.2 _ edge tail
      simp_all
      omega
    | pop _ tail => exact (hd a rfl rfl).elim
    | stay _ tail => exact (hd a rfl rfl).elim

/-- A proper segment forces a large stack at one of its two ends. -/
theorem proper_segment_budget {q : ℕ} (w : List (Fin q)) (hp : FusionProper w)
    (s t : List (Fin q)) (run : FusionEval s w t) :
    w.length ≤ s.length + t.length := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih =>
    have hd (v : List (Fin q)) : ∀ b ∈ w.head?, (a :: v).head? ≠ some b := by
      intro b hb eq
      have e : a = b := by simpa using eq
      subst b
      exact hp.1 hb
    cases run with
    | push _ _ tail =>
      have h := proper_push_length _ hp.2 _ _ (hd _) tail
      simp_all
      omega
    | pop _ tail =>
      have h := ih hp.2 _ tail
      simp_all
      omega
    | stay _ tail =>
      have h := proper_push_length _ hp.2 _ _ (hd _) tail
      simp_all
      omega

theorem fixed_cap_forbids_segment {q : ℕ} (H : ℕ) (w : List (Fin q))
    (hp : FusionProper w) (long : 2*H < w.length)
    (s t : List (Fin q)) (hs : s.length ≤ H) (ht : t.length ≤ H) :
    ¬ FusionEval s w t := by
  intro run
  have h := proper_segment_budget w hp s t run
  omega

private def altWord : ℕ → Bool → List (Fin 3)
  | 0, _ => []
  | n+1, b => (if b then 1 else 0) :: altWord n (!b)

private theorem alt_prop (n : ℕ) (b : Bool) :
    FusionProper (altWord n b) ∧ (altWord n b).length = n := by
  induction n generalizing b with
  | zero => exact ⟨trivial,rfl⟩
  | succ n ih =>
    obtain ⟨hp,hl⟩ := ih (!b)
    constructor
    · exact ⟨by cases n <;> cases b <;> norm_num [altWord] <;> decide, hp⟩
    · simpa [altWord] using hl

/-- Each aligned length-(2H+1) block in a run capped at its boundaries
must avoid a particular word. Counting all such block tuples independently
still gives a strict exponential loss for every fixed H. -/
theorem capped_block_count (H m : ℕ) :
    Nat.card {f : Fin m → (Fin (2*H+1) → Fin 3) //
      ∀ i, ∃ s t, s.length ≤ H ∧ t.length ≤ H ∧ FusionEval s (List.ofFn (f i)) t}
      ≤ (3^(2*H+1)-1)^m := by
  classical
  let b := 2*H+1
  let w := altWord b false
  obtain ⟨hp,hl⟩ := alt_prop b false
  let v : Fin b → Fin 3 := fun i => w.get (i.cast hl.symm)
  have hv : List.ofFn v = w := by
    exact (List.ofFn_congr (show w.length = b from hl) w.get).symm.trans (List.ofFn_get w)
  let F (f : {f : Fin m → (Fin b → Fin 3) //
      ∀ i, ∃ s t, s.length ≤ H ∧ t.length ≤ H ∧ FusionEval s (List.ofFn (f i)) t}) :
      Fin m → {u : Fin b → Fin 3 // u ≠ v} :=
    fun i => ⟨f.val i,by
      intro eq
      obtain ⟨s,t,hs,ht,run⟩ := f.property i
      rw [eq,hv] at run
      exact fixed_cap_forbids_segment H w hp (by dsimp [w]; rw [hl]; omega) s t hs ht run⟩
  have inj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun g => (g i).val) h
  have bound := Nat.card_le_card_of_injective F inj
  simpa [Nat.card_fun,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,b] using bound

#print axioms capped_block_count
#print axioms fixed_cap_forbids_segment
#print axioms full_iff_finite_blocks
end LC004.RawGrowth

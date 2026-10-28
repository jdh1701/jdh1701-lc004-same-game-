import LC004.RawCertificateEquivalence

namespace LC004
open scoped BigOperators

/-- A color occurring once cannot disappear in any winning history. -/
theorem insertion_history_count_ne_one {q : Nat} {w : List (Fin q)}
    (h : InsertionHistory w) : ∀ a, w.count a ≠ 1 := by
  induction h with
  | empty => simp
  | pair left right a smaller ih =>
      intro c
      by_cases hc : c = a
      · subst c
        simp only [List.count_append, List.count_cons_self, List.count_nil]
        omega
      · simpa [List.count_append, hc, Ne.symm hc] using ih c
  | triple left right a smaller ih =>
      intro c
      by_cases hc : c = a
      · subst c
        simp only [List.count_append, List.count_cons_self, List.count_nil]
        omega
      · simpa [List.count_append, hc, Ne.symm hc] using ih c

theorem raw_win_count_ne_one {q : Nat} {w : List (Fin q)}
    (hwin : RawMaxErases w []) : ∀ a, w.count a ≠ 1 :=
  insertion_history_count_ne_one ((raw_max_win_iff_insertion_history w).mp hwin)

theorem raw_win_count_ge_two {q : Nat} {w : List (Fin q)}
    (hwin : RawMaxErases w []) {a : Fin q} (ha : a ∈ w.toFinset) :
    2 ≤ w.count a := by
  have hp := List.count_pos_iff.mpr (List.mem_toFinset.mp ha)
  have hn := raw_win_count_ne_one hwin a
  omega

/-- Classify every way a finite family of nonnegative integers sums
to two. This makes the multiplicity reduction independent of tests. -/
theorem finset_nat_sum_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Nat) (hsum : ∑ a ∈ s, f a = 2) :
    (∃ a ∈ s, f a = 2 ∧ ∀ b ∈ s, b ≠ a → f b = 0) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = 1 ∧ f b = 1 ∧
      ∀ c ∈ s, c ≠ a → c ≠ b → f c = 0) := by
  classical
  have hbound (a : α) (ha : a ∈ s) : f a ≤ 2 := by
    have hh := Finset.single_le_sum (fun b (_ : b ∈ s) => Nat.zero_le (f b)) ha
    omega
  have hex (t : Finset α) (ht : ∑ a ∈ t, f a ≠ 0) :
      ∃ a ∈ t, f a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ht (Finset.sum_eq_zero h)
  by_cases htwo : ∃ a ∈ s, f a = 2
  · obtain ⟨a, ha, hfa⟩ := htwo
    left
    refine ⟨a, ha, hfa, ?_⟩
    have he := Finset.sum_erase_add s f ha
    have hz : ∑ b ∈ s.erase a, f b = 0 := by omega
    intro b hb hba
    have hbe : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
    have hh := Finset.single_le_sum
      (fun c (_ : c ∈ s.erase a) => Nat.zero_le (f c)) hbe
    omega
  · obtain ⟨a, ha, hfaNe⟩ := hex s (by omega)
    have hfaNot : f a ≠ 2 := by intro h; exact htwo ⟨a, ha, h⟩
    have hfaBound := hbound a ha
    have hfa : f a = 1 := by omega
    have he := Finset.sum_erase_add s f ha
    have hes : ∑ c ∈ s.erase a, f c = 1 := by omega
    obtain ⟨b, hb, hfbNe⟩ := hex (s.erase a) (by omega)
    have hfbBound := Finset.single_le_sum
      (fun c (_ : c ∈ s.erase a) => Nat.zero_le (f c)) hb
    have hfb : f b = 1 := by omega
    have hba := (Finset.mem_erase.mp hb).1
    have hbOrig := (Finset.mem_erase.mp hb).2
    have he2 := Finset.sum_erase_add (s.erase a) f hb
    have hz : ∑ c ∈ (s.erase a).erase b, f c = 0 := by omega
    right
    refine ⟨a, ha, b, hbOrig, Ne.symm hba, hfa, hfb, ?_⟩
    intro c hc hca hcb
    have hce : c ∈ (s.erase a).erase b :=
      Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, hc⟩⟩
    have hh := Finset.single_le_sum
      (fun d (_ : d ∈ (s.erase a).erase b) => Nat.zero_le (f d)) hce
    omega

def FourfoldProfile {q : Nat} (w : List (Fin q)) : Prop :=
  ∃ a ∈ w.toFinset, w.count a = 4 ∧
    ∀ b ∈ w.toFinset, b ≠ a → w.count b = 2

def TwoTripleProfile {q : Nat} (w : List (Fin q)) : Prop :=
  ∃ a ∈ w.toFinset, ∃ b ∈ w.toFinset,
    a ≠ b ∧ w.count a = 3 ∧ w.count b = 3 ∧
    ∀ c ∈ w.toFinset, c ≠ a → c ≠ b → w.count c = 2

/-- Every winning word on the second diagonal has precisely one of
the two multiplicity profiles needed in the proposed counting law. -/
theorem raw_win_second_diagonal_profiles {q : Nat} {w : List (Fin q)}
    (hwin : RawMaxErases w [])
    (hlen : w.length = 2 * w.toFinset.card + 2) :
    FourfoldProfile w ∨ TwoTripleProfile w := by
  classical
  let s := w.toFinset
  have hmin : ∀ a ∈ s, 2 ≤ w.count a := fun a ha => raw_win_count_ge_two hwin ha
  have hsum : (∑ a ∈ s, w.count a) = w.length :=
    List.sum_toFinset_count_eq_length w
  have hdecomp : (∑ a ∈ s, w.count a) =
      (∑ a ∈ s, (w.count a - 2)) + 2 * s.card := by
    calc
      _ = ∑ a ∈ s, ((w.count a - 2) + 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hh := hmin a ha
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  have hexcess : (∑ a ∈ s, (w.count a - 2)) = 2 := by omega
  rcases finset_nat_sum_two s (fun a => w.count a - 2) hexcess with hfour | hthree
  · obtain ⟨a, ha, hfa, hrest⟩ := hfour
    left
    refine ⟨a, ha, ?_, ?_⟩
    · have hh := hmin a ha
      omega
    · intro b hb hba
      have hz := hrest b hb hba
      have hh := hmin b hb
      omega
  · obtain ⟨a, ha, b, hb, hne, hfa, hfb, hrest⟩ := hthree
    right
    refine ⟨a, ha, b, hb, hne, ?_, ?_, ?_⟩
    · have hh := hmin a ha
      omega
    · have hh := hmin b hb
      omega
    · intro c hc hca hcb
      have hz := hrest c hc hca hcb
      have hh := hmin c hc
      omega

theorem second_diagonal_profiles_disjoint {q : Nat} (w : List (Fin q)) :
    ¬ (FourfoldProfile w ∧ TwoTripleProfile w) := by
  rintro ⟨⟨a, ha, hfour, _⟩, ⟨b, hb, c, hc, hbc, hb3, hc3, hrest⟩⟩
  by_cases hab : a = b
  · subst b
    omega
  · by_cases hac : a = c
    · subst c
      omega
    · have ha2 := hrest a ha hab hac
      omega

#print axioms raw_win_count_ge_two
#print axioms raw_win_second_diagonal_profiles
#print axioms second_diagonal_profiles_disjoint

end LC004

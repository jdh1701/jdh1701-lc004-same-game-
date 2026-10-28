import LC004.MatchingRepresentationCardinality
import LC004.TwoTripleCorrespondence
import LC004.SecondDiagonalProfiles

namespace LC004
open scoped BigOperators

theorem patternQuotientFiber_mk_eq_class {n : Nat} (p : ColorPattern n) (i : Fin n) :
    patternQuotientFiber p (Quotient.mk p i) = patternClassPositions p i := by
  rw [patternQuotientFiber_eq_class]
  have hout : p (Quotient.mk p i).out i := Quotient.mk_out i
  exact pattern_class_eq_of_related p hout

theorem related_out_iff_quotient_eq {n : Nat} (p : ColorPattern n) (i : Fin n) (q : Quotient p) :
    p i q.out ↔ Quotient.mk p i = q := by
  constructor
  · intro h
    exact (Quotient.sound h).trans (Quotient.out_eq q)
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq q).symm)

theorem out_related_iff_quotient_eq {n : Nat} (p : ColorPattern n) (q : Quotient p) (i : Fin n) :
    p q.out i ↔ Quotient.mk p i = q := by
  exact ⟨fun h => (related_out_iff_quotient_eq p i q).mp (p.symm h),
    fun h => p.symm ((related_out_iff_quotient_eq p i q).mpr h)⟩

open scoped Classical in
theorem pattern_sum_class_sizes {n : Nat} (p : ColorPattern n) :
    n = ∑ q : Quotient p, (patternQuotientFiber p q).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := Quotient.mk p)
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Quotient p)))
    (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin, patternQuotientFiber] using h

theorem winning_pattern_class_ge_two {n : Nat} (p : ColorPattern n)
    (hw : WinningColorPattern p) (i : Fin n) : 2 ≤ (patternClassPositions p i).card := by
  classical
  obtain ⟨cert⟩ := hw
  obtain ⟨b, hb, hi⟩ := cert.cover_position i
  have hle := Finset.card_le_card (certificate_block_subset_class p cert hb hi)
  have hn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  rw [List.toFinset_card_of_nodup hn] at hle
  rcases cert.sizes b hb with h | h <;> omega

/-- Exhaustive intrinsic profile split, directly for the finite target
space, with no conversion through named-color words. -/
theorem winning_intrinsic_second_diagonal_profiles {n : Nat} (p : ColorPattern n)
    (hw : WinningColorPattern p) (hlen : n = 2 * colorPatternClassCount p + 2) :
    FourfoldPairPattern p ∨ TwoTriplePairPattern p := by
  classical
  let s := (Finset.univ : Finset (Quotient p))
  let f := fun q : Quotient p => (patternQuotientFiber p q).card
  have hmin (q : Quotient p) : 2 ≤ f q := by
    simpa only [f, patternQuotientFiber_eq_class] using winning_pattern_class_ge_two p hw q.out
  have hsum : n = ∑ q ∈ s, f q := pattern_sum_class_sizes p
  have hcard : s.card = colorPatternClassCount p := by
    simp only [s, Finset.card_univ, colorPatternClassCount, Nat.card_eq_fintype_card]
  have hdecomp : (∑ q ∈ s, f q) = (∑ q ∈ s, (f q - 2)) + 2 * s.card := by
    calc
      _ = ∑ q ∈ s, ((f q - 2) + 2) := by
        apply Finset.sum_congr rfl
        intro q _
        have h := hmin q
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  have hexcess : (∑ q ∈ s, (f q - 2)) = 2 := by omega
  rcases finset_nat_sum_two s (fun q => f q - 2) hexcess with hfour | hthree
  · obtain ⟨q, _, hq, hrest⟩ := hfour
    left
    have hqsize : f q = 4 := by have h := hmin q; omega
    refine ⟨q.out, ?_, ?_⟩
    · simpa only [f, patternQuotientFiber_eq_class] using hqsize
    · intro i hnot
      have hne : Quotient.mk p i ≠ q := fun h => hnot ((out_related_iff_quotient_eq p q i).mpr h)
      have hz := hrest (Quotient.mk p i) (Finset.mem_univ _) hne
      have hm := hmin (Quotient.mk p i)
      have hsize : f (Quotient.mk p i) = 2 := by omega
      simpa only [f, patternQuotientFiber_mk_eq_class] using hsize
  · obtain ⟨q, _, r, _, hqr, hq, hr, hrest⟩ := hthree
    right
    have hqsize : f q = 3 := by have h := hmin q; omega
    have hrsize : f r = 3 := by have h := hmin r; omega
    refine ⟨q.out, r.out, ?_, ?_, ?_, ?_⟩
    · intro h
      have he := (related_out_iff_quotient_eq p q.out r).mp h
      exact hqr ((Quotient.out_eq q).symm.trans he)
    · simpa only [f, patternQuotientFiber_eq_class] using hqsize
    · simpa only [f, patternQuotientFiber_eq_class] using hrsize
    · intro i hnq hnr
      have hiq : Quotient.mk p i ≠ q := fun h => hnq ((out_related_iff_quotient_eq p q i).mpr h)
      have hir : Quotient.mk p i ≠ r := fun h => hnr ((out_related_iff_quotient_eq p r i).mpr h)
      have hz := hrest (Quotient.mk p i) (Finset.mem_univ _) hiq hir
      have hm := hmin (Quotient.mk p i)
      have hsize : f (Quotient.mk p i) = 2 := by omega
      simpa only [f, patternQuotientFiber_mk_eq_class] using hsize

theorem intrinsic_diagonal_profiles_disjoint {n : Nat} (p : ColorPattern n)
    (hf : FourfoldPairPattern p) (ht : TwoTriplePairPattern p) : False := by
  obtain ⟨a, ha, _⟩ := hf
  rcases two_triple_profile_small_classes p ht a with h | h <;> omega

theorem sum_one_four_rest_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Nat) {a : α} (ha : a ∈ s)
    (hfa : f a = 4) (hrest : ∀ b ∈ s, b ≠ a → f b = 2) :
    (∑ b ∈ s, f b) = 2 * s.card + 2 := by
  have he := Finset.sum_erase_add s f ha
  have hc := Finset.card_erase_add_one ha
  have hs : (∑ b ∈ s.erase a, f b) = 2 * (s.erase a).card := by
    calc
      _ = ∑ _b ∈ s.erase a, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hrest b (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem sum_two_triples_rest_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Nat) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hne : a ≠ b) (hfa : f a = 3) (hfb : f b = 3)
    (hrest : ∀ c ∈ s, c ≠ a → c ≠ b → f c = 2) :
    (∑ c ∈ s, f c) = 2 * s.card + 2 := by
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hne.symm, hb⟩
  have he1 := Finset.sum_erase_add s f ha
  have he2 := Finset.sum_erase_add (s.erase a) f hb'
  have hc1 := Finset.card_erase_add_one ha
  have hc2 := Finset.card_erase_add_one hb'
  have hs : (∑ c ∈ (s.erase a).erase b, f c) = 2 * ((s.erase a).erase b).card := by
    calc
      _ = ∑ _c ∈ (s.erase a).erase b, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcb := (Finset.mem_erase.mp hc).1
        have hca := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        have hcs := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
        exact hrest c hcs hca hcb
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem fourfold_profile_position_count {n : Nat} (p : ColorPattern n)
    (hp : FourfoldPairPattern p) : n = 2 * colorPatternClassCount p + 2 := by
  classical
  obtain ⟨a, ha, hrest⟩ := hp
  have hfour : (patternQuotientFiber p (Quotient.mk p a)).card = 4 := by
    rw [patternQuotientFiber_mk_eq_class]
    exact ha
  have hsum := sum_one_four_rest_two (Finset.univ : Finset (Quotient p))
    (fun q => (patternQuotientFiber p q).card) (Finset.mem_univ (Quotient.mk p a)) hfour
    (by
      intro q _ hq
      have hn : ¬ p a q.out := fun h => hq ((related_out_iff_quotient_eq p a q).mp h).symm
      change (patternQuotientFiber p q).card = 2
      rw [patternQuotientFiber_eq_class]
      exact hrest q.out hn)
  have hn := pattern_sum_class_sizes p
  simp only [Finset.card_univ, colorPatternClassCount, Nat.card_eq_fintype_card] at *
  omega

theorem two_triple_profile_position_count {n : Nat} (p : ColorPattern n)
    (hp : TwoTriplePairPattern p) : n = 2 * colorPatternClassCount p + 2 := by
  classical
  obtain ⟨a, b, hab, ha, hb, hrest⟩ := hp
  have hne : Quotient.mk p a ≠ Quotient.mk p b := fun h => hab (Quotient.exact h)
  have hfa : (patternQuotientFiber p (Quotient.mk p a)).card = 3 := by
    rw [patternQuotientFiber_mk_eq_class]; exact ha
  have hfb : (patternQuotientFiber p (Quotient.mk p b)).card = 3 := by
    rw [patternQuotientFiber_mk_eq_class]; exact hb
  have hsum := sum_two_triples_rest_two (Finset.univ : Finset (Quotient p))
    (fun q => (patternQuotientFiber p q).card) (Finset.mem_univ (Quotient.mk p a))
    (Finset.mem_univ (Quotient.mk p b)) hne hfa hfb
    (by
      intro q _ hqa hqb
      have hna : ¬ p a q.out := fun h => hqa ((related_out_iff_quotient_eq p a q).mp h).symm
      have hnb : ¬ p b q.out := fun h => hqb ((related_out_iff_quotient_eq p b q).mp h).symm
      change (patternQuotientFiber p q).card = 2
      change (patternQuotientFiber p q).card = 2
      rw [patternQuotientFiber_eq_class]
      exact hrest q.out hna hnb)
  have hn := pattern_sum_class_sizes p
  simp only [Finset.card_univ, colorPatternClassCount, Nat.card_eq_fintype_card] at *
  omega

#print axioms winning_intrinsic_second_diagonal_profiles
#print axioms fourfold_profile_position_count
#print axioms two_triple_profile_position_count

end LC004

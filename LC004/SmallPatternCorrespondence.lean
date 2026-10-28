import LC004.CertificatePairRefinement

namespace LC004

/-- Conventional noncrossing partitions forbid alternating positions
from distinct classes. Four positions inside one class are allowed. -/
def PatternNoncrossing {n : Nat} (p : ColorPattern n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → p a c → p b d → p a b

/-- The stronger condition used by size-two/three block certificates. -/
def PatternNoAlternation {n : Nat} (p : ColorPattern n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → ¬ (p a c ∧ p b d)

theorem four_related_positions_card_ge_four {n : Nat} (p : ColorPattern n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hpab : p a b) (hpac : p a c) (hpad : p a d) :
    4 ≤ (patternClassPositions p a).card := by
  classical
  have hnab : a ≠ b := by omega
  have hnac : a ≠ c := by omega
  have hnad : a ≠ d := by omega
  have hnbc : b ≠ c := by omega
  have hnbd : b ≠ d := by omega
  have hncd : c ≠ d := by omega
  have hcard : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
    simp [hnab, hnac, hnad, hnbc, hnbd, hncd]
  have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ patternClassPositions p a := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hax : p a x := hx.elim (fun h => h ▸ p.refl a)
      (fun h => h.elim (fun h => h.symm ▸ hpab)
        (fun h => h.elim (fun h => h.symm ▸ hpac) (fun h => h.symm ▸ hpad)))
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hax
  have hle := Finset.card_le_card hsub
  omega

theorem small_noncrossing_no_alternation {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card ≤ 3)
    (hnc : PatternNoncrossing p) : PatternNoAlternation p := by
  intro a b c d hab hbc hcd hcross
  have hpab := hnc a b c d hab hbc hcd hcross.1 hcross.2
  have hpad := p.trans hpab hcross.2
  have hge := four_related_positions_card_ge_four p hab hbc hcd hpab hcross.1 hpad
  have hle := hsmall a
  omega

theorem no_alternation_noncrossing {n : Nat} (p : ColorPattern n)
    (hno : PatternNoAlternation p) : PatternNoncrossing p := by
  intro a b c d hab hbc hcd hac hbd
  exact (hno a b c d hab hbc hcd ⟨hac, hbd⟩).elim

theorem patternQuotientFiber_eq_class {n : Nat} (p : ColorPattern n) (q : Quotient p) :
    patternQuotientFiber p q = patternClassPositions p q.out := by
  classical
  ext i
  simp only [mem_patternQuotientFiber, patternClassPositions,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact p.symm (Quotient.exact (h.trans (Quotient.out_eq q).symm))
  · intro h
    exact (Quotient.sound (p.symm h)).trans (Quotient.out_eq q)

/-- When every original class has size two or three, no certificate
can split a class: any proper block leaves at most one position. -/
theorem certificate_small_block_eq_class {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3)
    (cert : Noncrossing23Certificate (patternColor p))
    {b : List (Fin n)} (hb : b ∈ cert.blocks) {i : Fin n} (hi : i ∈ b) :
    b.toFinset = patternClassPositions p i := by
  classical
  have hsub := certificate_block_subset_class p cert hb hi
  apply Finset.eq_of_subset_of_card_le hsub
  by_contra hnot
  have hbn := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  have hbc := List.toFinset_card_of_nodup hbn
  have hblen := cert.sizes b hb
  have hclass := hsmall i
  have hdiff : ((patternClassPositions p i) \ b.toFinset).card = 1 := by
    rw [Finset.card_sdiff hsub]
    rcases hclass with h | h <;> rcases hblen with hlen | hlen <;> omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 <
    ((patternClassPositions p i) \ b.toFinset).card by omega)
  have hjc := (Finset.mem_sdiff.mp hj).1
  have hjnot := (Finset.mem_sdiff.mp hj).2
  have hij : p i j := by
    simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using hjc
  obtain ⟨c, hc, hjmem⟩ := cert.cover_position j
  have hne : b ≠ c := by
    intro heq
    exact hjnot (List.mem_toFinset.mpr (heq.symm ▸ hjmem))
  have hdis := disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hc hne
  have hcsub : c.toFinset ⊆ (patternClassPositions p i) \ b.toFinset := by
    intro x hx
    have hxc := List.mem_toFinset.mp hx
    have hjx : p j x := by
      have h := certificate_block_subset_class p cert hc hjmem hx
      simpa only [patternClassPositions, Finset.mem_filter, Finset.mem_univ, true_and] using h
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [patternClassPositions, Finset.mem_filter,
        Finset.mem_univ, true_and] using p.trans hij hjx
    · intro hxb
      exact (List.disjoint_left.mp hdis) (List.mem_toFinset.mp hxb) hxc
  have hcle := Finset.card_le_card hcsub
  have hcn := (List.nodup_flatten.mp cert.flatten_nodup).1 c hc
  have hclen := cert.sizes c hc
  rw [List.toFinset_card_of_nodup hcn, hdiff] at hcle
  rcases hclen with h | h <;> omega

theorem winning_small_no_alternation {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3)
    (hwin : WinningColorPattern p) : PatternNoAlternation p := by
  obtain ⟨cert⟩ := hwin
  intro a b c d hab hbc hcd hcross
  obtain ⟨ablock, ha, hap⟩ := cert.cover_position a
  obtain ⟨bblock, hb, hbp⟩ := cert.cover_position b
  have hac := certificate_small_block_eq_class p hsmall cert ha hap
  have hbd := certificate_small_block_eq_class p hsmall cert hb hbp
  have hc : c ∈ ablock := by
    apply List.mem_toFinset.mp
    rw [hac]
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcross.1
  have hd : d ∈ bblock := by
    apply List.mem_toFinset.mp
    rw [hbd]
    simpa only [patternClassPositions, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcross.2
  exact cert.no_alternation ha hb hap hc hbp hd (Or.inl ⟨hab, hbc, hcd⟩)

theorem no_alternation_fibers_no_cross {n : Nat} (p : ColorPattern n)
    (hno : PatternNoAlternation p) (q r : Quotient p) :
    ¬ BlocksCross ((patternQuotientFiber p q).toList.map Fin.val)
      ((patternQuotientFiber p r).toList.map Fin.val) := by
  classical
  rintro ⟨u, hu, v, hv, s, hs, t, ht, hcross⟩
  obtain ⟨iu, hiu, heu⟩ := List.mem_map.mp hu
  obtain ⟨iv, hiv, hev⟩ := List.mem_map.mp hv
  obtain ⟨is, his, hes⟩ := List.mem_map.mp hs
  obtain ⟨it, hit, het⟩ := List.mem_map.mp ht
  have huq : Quotient.mk p iu = q := by simpa using hiu
  have hvq : Quotient.mk p iv = q := by simpa using hiv
  have hsr : Quotient.mk p is = r := by simpa using his
  have htr : Quotient.mk p it = r := by simpa using hit
  have huv : p iu iv := Quotient.exact (huq.trans hvq.symm)
  have hst : p is it := Quotient.exact (hsr.trans htr.symm)
  have hc : PairCross iu.val iv.val is.val it.val := by
    simpa only [heu, hev, hes, het] using hcross
  rcases hc with ⟨hus, hsv, hvt⟩ | ⟨hsu, hut, htv⟩
  · exact hno iu is iv it hus hsv hvt ⟨huv, hst⟩
  · exact hno is iu it iv hsu hut htv ⟨hst, huv⟩

noncomputable def smallPatternCertificate {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3)
    (hnc : PatternNoncrossing p) : Noncrossing23Certificate (patternColor p) where
  blocks := patternBlockLists p
  sizes := by
    intro b hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    rw [Finset.length_toList, patternQuotientFiber_eq_class]
    exact hsmall q.out
  exactCover := patternBlockLists_exact_cover p
  monochromatic := by
    intro b hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    refine ⟨q.out, ?_⟩
    intro i hi
    have hq : Quotient.mk p i = q := by simpa using hi
    exact congrArg Quotient.out hq
  noncrossing := by
    intro xs hxs ys hys
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hys
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    apply no_alternation_fibers_no_cross p _ q r
    apply small_noncrossing_no_alternation p _ hnc
    intro i
    rcases hsmall i with h | h <;> omega

/-- Complete conventional noncrossing characterization whenever every
color occurs two or three times. No enumeration hypothesis is used. -/
theorem winning_small_pattern_iff_noncrossing {n : Nat} (p : ColorPattern n)
    (hsmall : ∀ i, (patternClassPositions p i).card = 2 ∨
      (patternClassPositions p i).card = 3) :
    WinningColorPattern p ↔ PatternNoncrossing p :=
  ⟨fun h => no_alternation_noncrossing p (winning_small_no_alternation p hsmall h),
    fun h => ⟨smallPatternCertificate p hsmall h⟩⟩

#print axioms certificate_small_block_eq_class
#print axioms winning_small_pattern_iff_noncrossing

end LC004

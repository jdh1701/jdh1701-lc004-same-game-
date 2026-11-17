import LC004.HeavyFaceRestriction

namespace LC004

/-- Assemble equivalence relations on disjoint ordered regions covering all
positions. No finiteness assumption on the region index is needed. -/
def assembledPattern {n : Nat} {ι : Type*} {m : ι → Nat}
    (e : ∀ k, Fin (m k) ↪o Fin n) (c : ∀ k, ColorPattern (m k))
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l) : ColorPattern n where
  r a b := ∃ k i j, e k i = a ∧ e k j = b ∧ c k i j
  iseqv := by
    constructor
    · intro a
      obtain ⟨k, i, rfl⟩ := cover a
      exact ⟨k, i, i, rfl, rfl, (c k).refl i⟩
    · rintro a b ⟨k, i, j, hi, hj, hij⟩
      exact ⟨k, j, i, hj, hi, (c k).symm hij⟩
    · rintro a b d ⟨k, i, j, hi, hj, hij⟩ ⟨l, s, t, hs, ht, hst⟩
      have hkl := disjoint k l j s (hj.trans hs.symm)
      subst l
      have hjs := (e k).injective (hj.trans hs.symm)
      subst s
      exact ⟨k, i, t, hi, ht, (c k).trans hij hst⟩

theorem assembledPattern_local {n : Nat} {ι : Type*} {m : ι → Nat}
    (e : ∀ k, Fin (m k) ↪o Fin n) (c : ∀ k, ColorPattern (m k))
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l)
    (k : ι) (i j : Fin (m k)) :
    assembledPattern e c cover disjoint (e k i) (e k j) ↔ c k i j := by
  constructor
  · rintro ⟨l, s, t, hs, ht, hst⟩
    have h := disjoint l k s i hs
    subst l
    have hsi := (e k).injective hs
    have htj := (e k).injective ht
    subst s
    subst t
    exact hst
  · intro h
    exact ⟨k, i, j, rfl, rfl, h⟩

/-- Local certificate partitions glue without introducing a crossing when
alternating pairs must belong to the same region. -/
theorem assembledPattern_constraint {n : Nat} {ι : Type*} {m : ι → Nat}
    (e : ∀ k, Fin (m k) ↪o Fin n) (c : ∀ k, ColorPattern (m k))
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l)
    (noncrossing : ∀ k l i j s t,
      e k i < e l s → e l s < e k j → e k j < e l t → k = l)
    (hc : ∀ k, CertificateConstraint (c k)) :
    CertificateConstraint (assembledPattern e c cover disjoint) := by
  let g := assembledPattern e c cover disjoint
  have local_eq (k : ι) : restrictColorPattern g (e k) = c k := by
    apply Setoid.ext
    intro i j
    exact (restrictColorPattern_rel g (e k) i j).trans
      (assembledPattern_local e c cover disjoint k i j)
  constructor
  · intro a
    obtain ⟨k, i, rfl⟩ := cover a
    have sat : ∀ i b, g (e k i) b → ∃ j, e k j = b := by
      rintro i b ⟨l, s, t, hs, ht, _⟩
      have h := disjoint l k s i hs
      subst l
      exact ⟨t, ht⟩
    have hcard := restrict_pattern_class_card g (e k) sat i
    rw [local_eq] at hcard
    change (patternClassPositions g (e k i)).card = 2 ∨ _
    rw [← hcard]
    exact (hc k).1 i
  · rintro a b d f hab hbd hdf ⟨k, i, j, rfl, rfl, hij⟩
      ⟨l, s, t, rfl, rfl, hst⟩
    have h := noncrossing k l i j s t hab hbd hdf
    subst l
    refine ⟨k, i, s, rfl, rfl, ?_⟩
    exact (hc k).2 i s j t ((e k).lt_iff_lt.mp hab)
      ((e k).lt_iff_lt.mp hbd) ((e k).lt_iff_lt.mp hdf) hij hst

/-- Winning restrictions on a disjoint noncrossing cover imply a global win.
The proof constructs a pair/triple partition and uses the established
certificate-to-maximal-deletion correspondence. -/
theorem winning_of_ordered_region_cover {n : Nat} {ι : Type*}
    (p : ColorPattern n) (m : ι → Nat) (e : ∀ k, Fin (m k) ↪o Fin n)
    (cover : ∀ a, ∃ k i, e k i = a)
    (disjoint : ∀ k l i j, e k i = e l j → k = l)
    (noncrossing : ∀ k l i j s t,
      e k i < e l s → e l s < e k j → e k j < e l t → k = l)
    (hwin : ∀ k, WinningColorPattern (restrictColorPattern p (e k))) :
    WinningColorPattern p := by
  classical
  have hex := fun k => (winning_iff_constraint_refinement _).mp (hwin k)
  choose c hc href using hex
  apply (winning_iff_constraint_refinement p).mpr
  refine ⟨assembledPattern e c cover disjoint,
    assembledPattern_constraint e c cover disjoint noncrossing hc, ?_⟩
  rintro a b ⟨k, i, j, rfl, rfl, hij⟩
  exact (restrictColorPattern_rel p (e k) i j).mp (href k hij)

/-- Finite-set interface to the ordered assembly theorem. -/
theorem winning_of_noncrossing_finset_cover {n : Nat} {ι : Type*}
    (p : ColorPattern n) (S : ι → Finset (Fin n))
    (cover : ∀ a, ∃ k, a ∈ S k)
    (disjoint : ∀ k l a, a ∈ S k → a ∈ S l → k = l)
    (noncrossing : ∀ k l a b c d, a < b → b < c → c < d →
      a ∈ S k → c ∈ S k → b ∈ S l → d ∈ S l → k = l)
    (hwin : ∀ k, WinningColorPattern
      (restrictColorPattern p ((S k).orderEmbOfFin rfl))) :
    WinningColorPattern p := by
  classical
  apply winning_of_ordered_region_cover p (fun k => (S k).card)
    (fun k => (S k).orderEmbOfFin rfl) ?_ ?_ ?_ hwin
  · intro a
    obtain ⟨k, hk⟩ := cover a
    refine ⟨k, ?_⟩
    have : a ∈ Set.range ((S k).orderEmbOfFin rfl) := by
      rwa [Finset.range_orderEmbOfFin]
    exact this
  · intro k l i j h
    apply disjoint k l ((S k).orderEmbOfFin rfl i)
      ((S k).orderEmbOfFin_mem rfl i)
    rw [h]
    exact (S l).orderEmbOfFin_mem rfl j
  · intro k l i j s t hab hbc hcd
    exact noncrossing k l _ _ _ _ hab hbc hcd
      ((S k).orderEmbOfFin_mem rfl i) ((S k).orderEmbOfFin_mem rfl j)
      ((S l).orderEmbOfFin_mem rfl s) ((S l).orderEmbOfFin_mem rfl t)

end LC004

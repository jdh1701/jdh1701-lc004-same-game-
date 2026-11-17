import LC004.SixClassSeparatorFacets

namespace LC004

/-- Boundary lists use the existing localNC6Color catalogue, not the Python
catalogue order. The six two-element lists form K_{2,3}; states 0,1,5 are the
three isolated two-triple certificates. -/
def sixBoundaryList : Fin 16 → Finset (Fin 8) :=
  ![∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7},
    {2,3}, {2,4}, {2,7}, {3,6}, {4,6}, {6,7}, Finset.univ]

theorem sixBoundary_intersection_closed : ∀ a b : Fin 16,
    ∃ c : Fin 16, sixBoundaryList a ∩ sixBoundaryList b = sixBoundaryList c := by
  decide +kernel

theorem sixBoundary_triple_helly : ∀ a b c : Fin 16,
    (sixBoundaryList a ∩ sixBoundaryList b).Nonempty →
    (sixBoundaryList a ∩ sixBoundaryList c).Nonempty →
    (sixBoundaryList b ∩ sixBoundaryList c).Nonempty →
    ((sixBoundaryList a ∩ sixBoundaryList b) ∩ sixBoundaryList c).Nonempty := by
  decide +kernel

theorem sixBoundary_proper_intersection_singleton : ∀ a b : Fin 16,
    a ≠ 15 → (sixBoundaryList a ∩ sixBoundaryList b).Nonempty →
    ¬ sixBoundaryList a ⊆ sixBoundaryList b →
    (sixBoundaryList a ∩ sixBoundaryList b).card = 1 := by
  decide +kernel

/-- Pairwise compatibility of boundary lists suffices for one common six-state,
for an arbitrary index type. There is no bound on the number of five-classes. -/
theorem sixBoundary_pairwise_helly {ι : Type*} (f : ι → Fin 16)
    (hpair : ∀ i j, (sixBoundaryList (f i) ∩ sixBoundaryList (f j)).Nonempty) :
    ∃ t : Fin 8, ∀ i, t ∈ sixBoundaryList (f i) := by
  classical
  by_cases hu : ∀ i, f i = 15
  · refine ⟨0, ?_⟩
    intro i
    rw [hu i]
    simp [sixBoundaryList]
  · push_neg at hu
    obtain ⟨i, hi⟩ := hu
    obtain ⟨x, hx⟩ := hpair i i
    have hxi := (Finset.mem_inter.mp hx).1
    by_cases hall : ∀ j, x ∈ sixBoundaryList (f j)
    · exact ⟨x, hall⟩
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      have hnsub : ¬ sixBoundaryList (f i) ⊆ sixBoundaryList (f j) :=
        fun hs => hj (hs hxi)
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp
        (sixBoundary_proper_intersection_singleton (f i) (f j) hi (hpair i j) hnsub)
      refine ⟨y, ?_⟩
      intro k
      obtain ⟨z, hz⟩ := sixBoundary_triple_helly (f i) (f j) (f k)
        (hpair i j) (hpair i k) (hpair j k)
      have hzy : z = y := by
        have hm := (Finset.mem_inter.mp hz).1
        rw [hy] at hm
        exact Finset.mem_singleton.mp hm
      exact hzy ▸ (Finset.mem_inter.mp hz).2

def SixBoundaryAdjacent (s t : Fin 8) : Prop :=
  s ≠ t ∧ ∃ e : Fin 6,
    s ∈ sixBoundaryList ⟨9 + e.val, by omega⟩ ∧
    t ∈ sixBoundaryList ⟨9 + e.val, by omega⟩

instance (s t : Fin 8) : Decidable (SixBoundaryAdjacent s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem sixBoundary_adjacent_iff_shared_cut : ∀ s t : Fin 8, s ≠ t →
    ((sixCertificateCutFacet s ∩ sixCertificateCutFacet t).Nonempty ↔
      SixBoundaryAdjacent s t) := by
  unfold sixCertificateCutFacet
  decide +kernel

theorem sixBoundary_no_triple_shared_cut : ∀ s t u : Fin 8,
    s ≠ t → s ≠ u → t ≠ u →
    (sixCertificateCutFacet s ∩ sixCertificateCutFacet t) ∩
      sixCertificateCutFacet u = ∅ := by
  unfold sixCertificateCutFacet
  decide +kernel

/-- The only two disjoint, mutually nonadjacent nonempty boundary fibres are
two singletons, or one matching edge and one isolated triple state. -/
theorem sixBoundary_two_fibres : ∀ a b : Fin 16,
    (sixBoundaryList a).Nonempty → (sixBoundaryList b).Nonempty →
    Disjoint (sixBoundaryList a) (sixBoundaryList b) →
    (∀ s ∈ sixBoundaryList a, ∀ t ∈ sixBoundaryList b,
      ¬ SixBoundaryAdjacent s t) →
    ((sixBoundaryList a).card = 1 ∧ (sixBoundaryList b).card = 1) ∨
    ((sixBoundaryList a).card = 2 ∧ ∃ t : Fin 8,
      sixBoundaryList b = {t} ∧ (t = 0 ∨ t = 1 ∨ t = 5)) ∨
    ((sixBoundaryList b).card = 2 ∧ ∃ t : Fin 8,
      sixBoundaryList a = {t} ∧ (t = 0 ∨ t = 1 ∨ t = 5)) := by
  decide +kernel

/-- Four open gaps in cyclic order J,K,I,L. In the split-pair case the triple
state permits I union J, K, L; the two-matching join permits J, I, K union L. -/
def sixTripleGapCell : Fin 4 → Fin 3 := ![0,1,0,2]
def sixMatchingGapCell : Fin 4 → Fin 3 := ![0,1,2,1]

/-- A doubled five-star has one root and two doubled endpoints. These local
constraints force all three into the same pair of opposite gaps. The mixed
certificate then uses blocks confined to individual gaps. -/
theorem sixFourGap_star_switch : ∀ r u v : Fin 4,
    sixTripleGapCell r = sixTripleGapCell u →
    sixMatchingGapCell r = sixMatchingGapCell v →
    (r.val % 2 = u.val % 2 ∧ r.val % 2 = v.val % 2) ∧
    (r.val % 2 = 0 → r = v) ∧ (r.val % 2 = 1 → r = u) := by
  decide +kernel

#print axioms sixBoundary_pairwise_helly
#print axioms sixBoundary_two_fibres
#print axioms sixFourGap_star_switch
end LC004

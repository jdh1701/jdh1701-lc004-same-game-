import LC004.ConnectedCoefficientSupport
import LC004.HeavyFaceCertificateProduct
import LC004.FourClassLocalPairs

namespace LC004
open scoped BigOperators Classical

/-- Contract the initial adjacent positions to the initial position. -/
def adjacentProjection {n : Nat} (i : Fin (n + 2)) : Fin (n + 1) :=
  ⟨i.val - 1, by omega⟩

@[simp] theorem adjacentProjection_zero {n : Nat} :
    adjacentProjection (0 : Fin (n + 2)) = 0 := rfl

@[simp] theorem adjacentProjection_succ {n : Nat} (i : Fin (n + 1)) :
    adjacentProjection i.succ = i := by
  apply Fin.ext
  simp [adjacentProjection]

theorem adjacentProjection_mono {n : Nat} :
    Monotone (@adjacentProjection n) := by
  intro a b h
  exact Nat.sub_le_sub_right h 1

def duplicateInitial {n : Nat} (p : ColorPattern (n + 1)) : ColorPattern (n + 2) :=
  Setoid.comap adjacentProjection p

def contractInitial {n : Nat} (p : ColorPattern (n + 2)) : ColorPattern (n + 1) :=
  Setoid.comap Fin.succ p

@[simp] theorem contract_duplicateInitial {n : Nat} (p : ColorPattern (n + 1)) :
    contractInitial (duplicateInitial p) = p := by
  ext a b
  change p (adjacentProjection a.succ) (adjacentProjection b.succ) ↔ p a b
  simp

theorem duplicateInitial_injective {n : Nat} :
    Function.Injective (@duplicateInitial n) := by
  intro p q h
  simpa using congrArg contractInitial h

theorem duplicate_contractInitial {n : Nat} (p : ColorPattern (n + 2))
    (h : p 0 (Fin.succ 0)) : duplicateInitial (contractInitial p) = p := by
  have hx (x : Fin (n + 2)) : p x (adjacentProjection x).succ := by
    induction x using Fin.cases with
    | zero => simpa using h
    | succ i =>
      change p i.succ i.succ
      exact p.refl _
  ext x y
  change p (adjacentProjection x).succ (adjacentProjection y).succ ↔ p x y
  exact ⟨fun hxy => p.trans (p.trans (hx x) hxy) (p.symm (hx y)),
    fun hxy => p.trans (p.trans (p.symm (hx x)) hxy) (hx y)⟩

/-- Monotone pullback cannot create a crossing between distinct classes. -/
theorem patternNoncrossing_monotone_comap {n m : Nat} (p : ColorPattern n)
    (f : Fin m → Fin n) (hf : Monotone f) (hp : PatternNoncrossing p) :
    PatternNoncrossing (Setoid.comap f p) := by
  intro a b c d hab hbc hcd hac hbd
  have h1 := hf (le_of_lt hab)
  have h2 := hf (le_of_lt hbc)
  have h3 := hf (le_of_lt hcd)
  change p (f a) (f c) at hac
  change p (f b) (f d) at hbd
  change p (f a) (f b)
  by_cases h : f a = f b
  · rw [h]
  by_cases k : f b = f c
  · simpa only [k] using hac
  by_cases l : f c = f d
  · exact p.trans hac (p.symm (by simpa only [l] using hbd))
  exact hp _ _ _ _ (lt_of_le_of_ne h1 h) (lt_of_le_of_ne h2 k)
    (lt_of_le_of_ne h3 l) hac hbd

theorem duplicateInitial_noncrossing_iff {n : Nat} (p : ColorPattern (n + 1)) :
    PatternNoncrossing (duplicateInitial p) ↔ PatternNoncrossing p := by
  constructor
  · intro h a b c d hab hbc hcd hac hbd
    have he := h a.succ b.succ c.succ d.succ (by omega) (by omega) (by omega)
    simpa [duplicateInitial, Setoid.comap] using he hac hbd
  · exact patternNoncrossing_monotone_comap p _ adjacentProjection_mono

/-- Connectedness is preserved in BOTH directions by adjacent duplication. -/
theorem duplicateInitial_connected_iff {n : Nat} (p : ColorPattern (n + 1)) :
    NCConnected (duplicateInitial p) ↔ NCConnected p := by
  rw [ncConnected_iff_no_proper_noncrossing_coarsening,
    ncConnected_iff_no_proper_noncrossing_coarsening]
  constructor
  · intro h q hpq hq
    have ht := h (duplicateInitial q) (fun _ _ hab => hpq hab)
      ((duplicateInitial_noncrossing_iff q).mpr hq)
    apply top_unique
    intro a b _
    have he : duplicateInitial q a.succ b.succ := by rw [ht]; trivial
    simpa [duplicateInitial, Setoid.comap] using he
  · intro h q hpq hq
    have hc : PatternNoncrossing (contractInitial q) :=
      patternNoncrossing_monotone_comap q Fin.succ (by intro a b hab; omega) hq
    have ht := h (contractInitial q) (by
      intro a b hab
      apply hpq
      simpa [duplicateInitial, Setoid.comap] using hab) hc
    have hpair : q 0 (Fin.succ 0) := hpq (by
      change p 0 0
      exact p.refl 0)
    rw [← duplicate_contractInitial q hpair, ht]
    rfl

/-- The duplicated point adds exactly one to its own equivalence class. -/
theorem duplicateInitial_class_card {n : Nat} (p : ColorPattern (n + 1))
    (x : Fin (n + 2)) :
    (patternClassPositions (duplicateInitial p) x).card =
      (if p (adjacentProjection x) 0 then 1 else 0) +
        (patternClassPositions p (adjacentProjection x)).card := by
  classical
  calc
    _ = ∑ i : Fin (n + 2), if duplicateInitial p x i then (1 : Nat) else 0 :=
      (Finset.sum_boole _ _).symm
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp only [duplicateInitial, Setoid.comap, adjacentProjection_zero,
        adjacentProjection_succ, Finset.sum_boole, patternClassPositions, Nat.cast_id]

theorem certificateConstraint_four_class_pair {n : Nat} (p c : ColorPattern n)
    (hc : CertificateConstraint c) (hle : c ≤ p) (i : Fin n)
    (hi : (patternClassPositions p i).card = 4) :
    (patternClassPositions c i).card = 2 := by
  let d : CertificatePartition p := ⟨c, hc, hle⟩
  have he := certificate_four_class_card p d.toCertificate i hi
  rwa [d.toCertificate_pattern] at he

/-- Exactly the pair-containing certificates duplicate to triple-containing ones. -/
theorem duplicateInitial_certificate_iff {n : Nat} (c : ColorPattern (n + 1)) :
    (CertificateConstraint (duplicateInitial c) ∧
      (patternClassPositions (duplicateInitial c) 0).card = 3) ↔
    (CertificateConstraint c ∧ (patternClassPositions c 0).card = 2) := by
  have hzero : (patternClassPositions (duplicateInitial c) 0).card =
      1 + (patternClassPositions c 0).card := by
    have h := duplicateInitial_class_card c 0
    change (patternClassPositions (duplicateInitial c) 0).card =
      (if c 0 0 then 1 else 0) + (patternClassPositions c 0).card at h
    rw [if_pos (show c 0 0 from c.refl 0)] at h
    exact h
  constructor
  · rintro ⟨hc, hcard⟩
    have htwo : (patternClassPositions c 0).card = 2 := by omega
    refine ⟨⟨?_, (duplicateInitial_noncrossing_iff c).mp hc.2⟩, htwo⟩
    intro i
    by_cases h : c i 0
    · rw [patternClassPositions_eq_of_related c h, htwo]
      exact Or.inl rfl
    · have hs := hc.1 i.succ
      have he := duplicateInitial_class_card c i.succ
      simp only [adjacentProjection_succ, if_neg h, zero_add] at he
      rwa [he] at hs
  · rintro ⟨hc, htwo⟩
    refine ⟨⟨?_, (duplicateInitial_noncrossing_iff c).mpr hc.2⟩, by omega⟩
    intro i
    rw [duplicateInitial_class_card]
    by_cases h : c (adjacentProjection i) 0
    · rw [if_pos h, patternClassPositions_eq_of_related c h, htwo]
      exact Or.inr rfl
    · rw [if_neg h, zero_add]
      exact hc.1 _

/-- This is the ACTUAL restricted original certificate family, not a local model. -/
def InitialTripleCertificate {n : Nat} (p c : ColorPattern (n + 2)) : Prop :=
  CertificateConstraint c ∧ c ≤ p ∧ c 0 (Fin.succ 0) ∧
    (patternClassPositions c 0).card = 3

/-- Deletion and duplication give a duplication-free correspondence, with all
other class sizes unrestricted. -/
theorem initialTripleCertificate_iff {n : Nat} (p : ColorPattern (n + 1))
    (hp : (patternClassPositions p 0).card = 4) (c : ColorPattern (n + 2)) :
    InitialTripleCertificate (duplicateInitial p) c ↔
      ∃ d : ColorPattern (n + 1), CertificateConstraint d ∧ d ≤ p ∧
        duplicateInitial d = c := by
  constructor
  · rintro ⟨hc, hle, hpair, hthree⟩
    have he := duplicate_contractInitial c hpair
    refine ⟨contractInitial c, ?_, ?_, he⟩
    · exact ((duplicateInitial_certificate_iff _).mp
        (by simpa only [he] using And.intro hc hthree)).1
    · intro a b hab
      have hx := hle hab
      simpa [duplicateInitial, Setoid.comap] using hx
  · rintro ⟨d, hd, hle, rfl⟩
    have htwo := certificateConstraint_four_class_pair p d hd hle 0 hp
    have hcert := (duplicateInitial_certificate_iff d).mpr ⟨hd, htwo⟩
    refine ⟨hcert.1, fun _ _ hab => hle hab, ?_, hcert.2⟩
    change d 0 0
    exact d.refl 0

/-- Pullback along the adjacent contraction preserves binary joins. -/
theorem duplicateInitial_sup {n : Nat} (p q : ColorPattern (n + 1)) :
    duplicateInitial (p ⊔ q) = duplicateInitial p ⊔ duplicateInitial q := by
  apply le_antisymm
  · let r := duplicateInitial p ⊔ duplicateInitial q
    have hp : duplicateInitial p ≤ r := le_sup_left
    have hq : duplicateInitial q ≤ r := le_sup_right
    have hle : p ⊔ q ≤ contractInitial r := sup_le (by
      intro a b hab
      exact hp (show duplicateInitial p a.succ b.succ from hab)) (by
      intro a b hab
      exact hq (show duplicateInitial q a.succ b.succ from hab))
    have hx (x : Fin (n + 2)) : r x (adjacentProjection x).succ := by
      apply hp
      change p (adjacentProjection x) (adjacentProjection x)
      exact p.refl _
    intro a b hab
    exact r.trans (r.trans (hx a) (hle hab)) (r.symm (hx b))
  · exact sup_le
      (fun _ _ hab => (show p ≤ p ⊔ q from le_sup_left) hab)
      (fun _ _ hab => (show q ≤ p ⊔ q from le_sup_right) hab)

theorem certificateJoinTerms_duplicateInitial {n : Nat}
    (cs : List (ColorPattern (n + 1))) :
    certificateJoinTerms (cs.map duplicateInitial) =
      (certificateJoinTerms cs).map (fun t => (duplicateInitial t.1, t.2)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, certificateJoinTerms, ih, List.map_append,
      List.map_map, duplicateInitial_sup, Function.comp_def]

theorem collectedJoinCoefficient_duplicateInitial {n : Nat}
    (cs : List (ColorPattern (n + 1))) (p : ColorPattern (n + 1)) :
    collectedJoinCoefficient (certificateJoinTerms (cs.map duplicateInitial))
        (duplicateInitial p) = collectedJoinCoefficient (certificateJoinTerms cs) p := by
  classical
  rw [certificateJoinTerms_duplicateInitial]
  simp only [collectedJoinCoefficient, List.map_map, Function.comp_def,
    duplicateInitial_injective.eq_iff]

noncomputable def initialTripleCertificates {n : Nat} (p : ColorPattern (n + 2)) :
    List (ColorPattern (n + 2)) :=
  (Finset.univ.filter (InitialTripleCertificate p)).toList

noncomputable def initialTripleCoefficient {n : Nat} (p : ColorPattern (n + 2)) : Int :=
  collectedJoinCoefficient (certificateJoinTerms (initialTripleCertificates p)) p

/-- Signed subset joins of the restricted ORIGINAL family equal the original
winning coefficient after deleting one position. No connectedness is needed. -/
theorem initialTripleCoefficient_eq_contracted {n : Nat} (p : ColorPattern (n + 1))
    (hp : (patternClassPositions p 0).card = 4) :
    initialTripleCoefficient (duplicateInitial p) = winningJoinCoefficient (n + 1) p := by
  classical
  let cs := (Finset.univ.filter (fun c => CertificateConstraint c ∧ c ≤ p)).toList
  have hcs (c) : c ∈ cs ↔ CertificateConstraint c ∧ c ≤ p := by simp [cs]
  have hm (c) : c ∈ cs.map duplicateInitial ↔
      c ∈ initialTripleCertificates (duplicateInitial p) := by
    simp only [List.mem_map, hcs, initialTripleCertificates, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and, initialTripleCertificate_iff p hp]
    constructor
    · rintro ⟨d, ⟨hd, hle⟩, he⟩
      exact ⟨d, hd, hle, he⟩
    · rintro ⟨d, hd, hle, he⟩
      exact ⟨d, ⟨hd, hle⟩, he⟩
  have he : collectedJoinCoefficient
      (certificateJoinTerms (initialTripleCertificates (duplicateInitial p))) =
      collectedJoinCoefficient (certificateJoinTerms (cs.map duplicateInitial)) := by
    apply lowerIncidence_injective
    funext r
    rw [collectedJoinCoefficient_incidence, collectedJoinCoefficient_incidence,
      certificateJoinTerms_score, certificateJoinTerms_score]
    simp only [hm]
  unfold initialTripleCoefficient
  rw [he, collectedJoinCoefficient_duplicateInitial]
  exact (winningJoinCoefficient_eq_local_generators p cs (fun c => (hcs c).symm)).symm

/-- The formerly open restricted cancellation, for any other class sizes. -/
theorem initialTripleCoefficient_zero {n : Nat} (p : ColorPattern (n + 2))
    (hc : NCConnected p) (hntop : p ≠ ⊤) (hpair : p 0 (Fin.succ 0))
    (hfive : (patternClassPositions p 0).card = 5) : initialTripleCoefficient p = 0 := by
  let q := contractInitial p
  have he : duplicateInitial q = p := duplicate_contractInitial p hpair
  have hfour : (patternClassPositions q 0).card = 4 := by
    have hcard := duplicateInitial_class_card q 0
    rw [he, hfive] at hcard
    change 5 = (if q 0 0 then 1 else 0) + (patternClassPositions q 0).card at hcard
    rw [if_pos (show q 0 0 from q.refl 0)] at hcard
    omega
  have hqc : NCConnected q := (duplicateInitial_connected_iff q).mp (he.symm ▸ hc)
  have hqt : q ≠ ⊤ := by
    intro h
    apply hntop
    rw [← he, h]
    rfl
  have hz : winningJoinCoefficient (n + 1) q = 0 := by
    by_contra hne
    have hge := ncConnected_nonzero_every_class_min_five q hqc hqt hne 0
    omega
  calc
    initialTripleCoefficient p = initialTripleCoefficient (duplicateInitial q) :=
      congrArg initialTripleCoefficient he.symm
    _ = winningJoinCoefficient (n + 1) q := initialTripleCoefficient_eq_contracted q hfour
    _ = 0 := hz

#print axioms duplicateInitial_connected_iff
#print axioms initialTripleCertificate_iff
#print axioms initialTripleCoefficient_eq_contracted
#print axioms initialTripleCoefficient_zero
end LC004

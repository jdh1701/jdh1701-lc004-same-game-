import LC004.ConnectedClassCrossing
import LC004.WinningConstraintGenerators
import LC004.LocalCertificateCatalogues

namespace LC004

/-- A chord shared by all generators traps every other color inside its open
interval. The class-gap premise removes the chord's own color from that interval. -/
theorem noncrossing_refinement_preserves_class_gap {n : Nat}
    (p c : ColorPattern n) (hcn : PatternNoncrossing c) (hle : c ≤ p)
    (u v : Fin n) (hcv : c u v)
    (hgap : ∀ x, u < x → x < v → ¬ p u x) :
    ∀ x y, c x y → (u < x ∧ x < v) → (u < y ∧ y < v) := by
  intro x y hxy hx
  have hpx : ¬ p u x := hgap x hx.1 hx.2
  have hpy : ¬ p u y := fun h => hpx (p.trans h (p.symm (hle hxy)))
  have hneU : y ≠ u := by intro h; subst y; exact hpy (p.refl u)
  have hneV : y ≠ v := by intro h; subst y; exact hpy (hle hcv)
  by_cases hyu : y < u
  · have hyux := hcn y u x v hyu hx.1 hx.2 (c.symm hxy) hcv
    exact (hpy (hle (c.symm hyux))).elim
  · by_cases hvy : v < y
    · exact (hpx (hle (hcn u x v y hx.1 hx.2 hvy hcv hxy))).elim
    · constructor <;> omega

/-- A shared chord across consecutive occurrences has no interior positions
when the noncrossing generators join to an intrinsically connected pattern. -/
theorem ncConnected_common_generator_gap_empty {n : Nat}
    (p : ColorPattern n) (hc : NCConnected p) (F : Finset (ColorPattern n))
    (hF : ∀ c ∈ F, PatternNoncrossing c) (hle : ∀ c ∈ F, c ≤ p)
    (hjoin : ∀ q : ColorPattern n, (∀ c ∈ F, c ≤ q) → p ≤ q)
    (u v : Fin n) (hcommon : ∀ c ∈ F, c u v)
    (hgap : ∀ x, u < x → x < v → ¬ p u x) :
    ∀ x, ¬ (u < x ∧ x < v) := by
  classical
  let P : Fin n → Prop := fun x => u < x ∧ x < v
  have hcut : ∀ c ∈ F, c ≤ predicateCut P := by
    intro c hcf x y hxy
    exact ⟨noncrossing_refinement_preserves_class_gap p c (hF c hcf) (hle c hcf)
        u v (hcommon c hcf) hgap x y hxy,
      noncrossing_refinement_preserves_class_gap p c (hF c hcf) (hle c hcf)
        u v (hcommon c hcf) hgap y x (c.symm hxy)⟩
  have hp := hjoin (predicateCut P) hcut
  intro x hx
  exact ncConnected_no_saturated_interval p hc P (by intros; dsimp [P] at *; omega)
    (fun a b hab ha => (hp hab).mp ha) x u hx (by dsimp [P]; omega)

/-- The two-generator specialization used in the all-five run theorem. -/
theorem ncConnected_pair_join_gap_adjacent {n : Nat}
    (p c d : ColorPattern n) (hc : NCConnected p)
    (hcn : PatternNoncrossing c) (hdn : PatternNoncrossing d) (hcd : c ⊔ d = p)
    (u v : Fin n) (huv : u < v) (hcu : c u v) (hdu : d u v)
    (hgap : ∀ x, u < x → x < v → ¬ p u x) : v.val = u.val + 1 := by
  classical
  have hcp : c ≤ p := by rw [← hcd]; exact le_sup_left
  have hdp : d ≤ p := by rw [← hcd]; exact le_sup_right
  have he := ncConnected_common_generator_gap_empty p hc {c,d}
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hcn
        · exact hdn)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hcp
        · exact hdp)
    (by intro q hq; rw [← hcd]; exact sup_le (hq c (by simp)) (hq d (by simp)))
    u v
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hcu
        · exact hdu)
    hgap
  by_contra h
  let x : Fin n := ⟨u.val+1, by omega⟩
  exact he x (by change u.val < u.val + 1 ∧ u.val + 1 < v.val; omega)

/-- The complementary circular gap: the closed interval is saturated when
its endpoints share a certificate block and their color is absent outside. -/
theorem noncrossing_refinement_preserves_closed_class_interval {n : Nat}
    (p c : ColorPattern n) (hcn : PatternNoncrossing c) (hle : c ≤ p)
    (u v : Fin n) (hcv : c u v)
    (hgap : ∀ x, ¬ (u ≤ x ∧ x ≤ v) → ¬ p u x) :
    ∀ x y, c x y → (u ≤ x ∧ x ≤ v) → (u ≤ y ∧ y ≤ v) := by
  intro x y hxy hx
  by_contra hy
  have hpy : ¬ p u y := hgap y hy
  have hpx : ¬ p u x := fun h => hpy (p.trans h (hle hxy))
  have hneU : x ≠ u := by intro h; subst x; exact hpx (p.refl u)
  have hneV : x ≠ v := by intro h; subst x; exact hpx (hle hcv)
  have hux : u < x := by omega
  have hxv : x < v := by omega
  by_cases hyu : y < u
  · exact hpy (hle (c.symm (hcn y u x v hyu hux hxv (c.symm hxy) hcv)))
  · have hvy : v < y := by omega
    exact hpx (hle (hcn u x v y hux hxv hvy hcv hxy))

/-- The wraparound case of the common-gap theorem, without assuming a
separate rotation-invariance bridge. -/
theorem ncConnected_common_generator_exterior_empty {n : Nat}
    (p : ColorPattern n) (hc : NCConnected p) (F : Finset (ColorPattern n))
    (hF : ∀ c ∈ F, PatternNoncrossing c) (hle : ∀ c ∈ F, c ≤ p)
    (hjoin : ∀ q : ColorPattern n, (∀ c ∈ F, c ≤ q) → p ≤ q)
    (u v : Fin n) (huv : u ≤ v) (hcommon : ∀ c ∈ F, c u v)
    (hgap : ∀ x, ¬ (u ≤ x ∧ x ≤ v) → ¬ p u x) :
    ∀ x, u ≤ x ∧ x ≤ v := by
  classical
  let P : Fin n → Prop := fun x => u ≤ x ∧ x ≤ v
  have hcut : ∀ c ∈ F, c ≤ predicateCut P := by
    intro c hcf x y hxy
    exact ⟨noncrossing_refinement_preserves_closed_class_interval p c
        (hF c hcf) (hle c hcf) u v (hcommon c hcf) hgap x y hxy,
      noncrossing_refinement_preserves_closed_class_interval p c
        (hF c hcf) (hle c hcf) u v (hcommon c hcf) hgap y x (c.symm hxy)⟩
  have hp := hjoin (predicateCut P) hcut
  intro x
  by_contra hx
  exact ncConnected_no_saturated_interval p hc P (by intros; dsimp [P] at *; omega)
    (fun a b hab ha => (hp hab).mp ha) u x ⟨le_refl u,huv⟩ hx

/-- The size-two block of each local five-point certificate. -/
def fivePairVertices (s : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter (fun i =>
    (Finset.univ.filter (fun j => localNC5Color s i = localNC5Color s j)).card = 2)

theorem five_pair_vertices_card : ∀ s : Fin 5, (fivePairVertices s).card = 2 := by
  unfold fivePairVertices localNC5Color
  decide +kernel

/-- Overlapping pair choices leave a cyclic edge in both triple blocks. -/
theorem five_overlapping_pairs_common_triple : ∀ s t : Fin 5, s ≠ t →
    ¬ Disjoint (fivePairVertices s) (fivePairVertices t) →
    ∃ i : Fin 5,
      localNC5Color s i = localNC5Color s (i+1) ∧
      localNC5Color t i = localNC5Color t (i+1) ∧
      i ∉ fivePairVertices s ∧ i ∉ fivePairVertices t := by
  unfold fivePairVertices localNC5Color
  decide +kernel

/-- With disjoint pair choices, each pair is a consecutive class edge and is
identified by BOTH certificates. Transport through the gap theorem makes it
an actual adjacent pair in the full pattern. -/
theorem five_disjoint_pair_common_edge : ∀ s t : Fin 5,
    Disjoint (fivePairVertices s) (fivePairVertices t) →
    ∃ i : Fin 5, fivePairVertices s = {i,i+1} ∧
      localNC5Color s i = localNC5Color s (i+1) ∧
      localNC5Color t i = localNC5Color t (i+1) := by
  unfold fivePairVertices localNC5Color
  decide +kernel

#print axioms ncConnected_common_generator_gap_empty
#print axioms ncConnected_pair_join_gap_adjacent
#print axioms ncConnected_common_generator_exterior_empty
#print axioms five_overlapping_pairs_common_triple
#print axioms five_disjoint_pair_common_edge
end LC004

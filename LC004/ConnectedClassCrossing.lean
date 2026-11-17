import LC004.NoncrossingClosure

namespace LC004
open scoped Classical

/-- The selected original class participates in a genuine crossing. -/
def PatternClassCrossed {n : Nat} (p : ColorPattern n) (a : Fin n) : Prop :=
  ∃ u v x y : Fin n, p a u ∧ p a v ∧ p x y ∧ ¬ p a x ∧
    ((u < x ∧ x < v ∧ v < y) ∨ (x < u ∧ u < y ∧ y < v))

def predicateCut {n : Nat} (P : Fin n → Prop) : ColorPattern n where
  r x y := P x ↔ P y
  iseqv := ⟨fun _ => Iff.rfl,fun h => h.symm,fun h k => h.trans k⟩

/-- An interval and its complement form a noncrossing two-part partition. -/
theorem predicateCut_noncrossing {n : Nat} (P : Fin n → Prop)
    (hconvex : ∀ a b c, a < b → b < c → P a → P c → P b) :
    PatternNoncrossing (predicateCut P) := by
  intro a b c d hab hbc hcd hac hbd
  change (P a ↔ P c) at hac
  change (P b ↔ P d) at hbd
  change P a ↔ P b
  exact ⟨fun ha => hconvex a b c hab hbc ha (hac.mp ha),
    fun hb => hac.mpr (hconvex b c d hbc hcd hb (hbd.mp hb))⟩

theorem ncConnected_no_saturated_interval {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (P : Fin n → Prop)
    (hconvex : ∀ a b c, a < b → b < c → P a → P c → P b)
    (hsat : ∀ x y, p x y → P x → P y)
    (a b : Fin n) (ha : P a) (hb : ¬ P b) : False := by
  have hle : p ≤ predicateCut P := fun x y h =>
    ⟨hsat x y h,hsat y x (p.symm h)⟩
  have he := (ncConnected_iff_no_proper_noncrossing_coarsening p).mp hc
    (predicateCut P) hle (predicateCut_noncrossing P hconvex)
  have hab : predicateCut P a b := by rw [he]; trivial
  exact hb (hab.mp ha)

/-- A nontrivial noncrossing-connected pattern has no isolated original class.
The proof separates an uncrossed class by a saturated interval gap. -/
theorem ncConnected_every_class_crossed {n : Nat} (p : ColorPattern n)
    (hc : NCConnected p) (hntop : p ≠ ⊤) (a : Fin n) :
    PatternClassCrossed p a := by
  classical
  by_contra hn
  have noCross (u v x y : Fin n) (hu : p a u) (hv : p a v)
      (hxy : p x y) (hax : ¬ p a x)
      (hord : (u < x ∧ x < v ∧ v < y) ∨ (x < u ∧ u < y ∧ y < v)) : False :=
    hn ⟨u,v,x,y,hu,hv,hxy,hax,hord⟩
  have hbex : ∃ b : Fin n, ¬ p a b := by
    by_contra h
    push_neg at h
    apply hntop
    apply top_unique
    intro x y _
    exact p.trans (p.symm (h x)) (h y)
  obtain ⟨b,hb⟩ := hbex
  let S := patternClassPositions p a
  have memS (x : Fin n) : x ∈ S ↔ p a x := by simp [S,patternClassPositions]
  have hS : S.Nonempty := ⟨a,(memS a).mpr (p.refl a)⟩
  let lo := S.min' hS
  let hi := S.max' hS
  have hlo : p a lo := (memS lo).mp (S.min'_mem hS)
  have hhi : p a hi := (memS hi).mp (S.max'_mem hS)
  have bounds (x : Fin n) (hx : p a x) : lo ≤ x ∧ x ≤ hi :=
    ⟨S.min'_le x ((memS x).mpr hx),S.le_max' x ((memS x).mpr hx)⟩
  by_cases hbmid : lo ≤ b ∧ b ≤ hi
  · have hlob : lo < b := lt_of_le_of_ne hbmid.1 (fun he => hb (he ▸ hlo))
    have hbhi : b < hi := lt_of_le_of_ne hbmid.2 (fun he => hb (he.symm ▸ hhi))
    let L := S.filter (· < b)
    let R := S.filter (b < ·)
    have hL : L.Nonempty := ⟨lo,Finset.mem_filter.mpr ⟨(memS lo).mpr hlo,hlob⟩⟩
    have hR : R.Nonempty := ⟨hi,Finset.mem_filter.mpr ⟨(memS hi).mpr hhi,hbhi⟩⟩
    let u := L.max' hL
    let v := R.min' hR
    have hu0 := Finset.mem_filter.mp (L.max'_mem hL)
    have hv0 := Finset.mem_filter.mp (R.min'_mem hR)
    have hu : p a u := (memS u).mp hu0.1
    have hv : p a v := (memS v).mp hv0.1
    have hub : u < b := hu0.2
    have hbv : b < v := hv0.2
    have gap (x : Fin n) (hux : u < x) (hxv : x < v) : ¬ p a x := by
      intro hx
      rcases lt_trichotomy x b with h | h | h
      · have hm : x ≤ u := L.le_max' x (Finset.mem_filter.mpr ⟨(memS x).mpr hx,h⟩)
        omega
      · exact hb (h ▸ hx)
      · have hm : v ≤ x := R.min'_le x (Finset.mem_filter.mpr ⟨(memS x).mpr hx,h⟩)
        omega
    apply ncConnected_no_saturated_interval p hc (fun x => u < x ∧ x < v)
      (by intros; omega) ?_ b u ⟨hub,hbv⟩ (by omega)
    intro x y hxy hx
    by_contra hy
    have hax := gap x hx.1 hx.2
    have hay : ¬ p a y := fun h => hax (p.trans h (p.symm hxy))
    have hneU : y ≠ u := fun h => hay (h.symm ▸ hu)
    have hneV : y ≠ v := fun h => hay (h.symm ▸ hv)
    by_cases hyu : y < u
    · exact noCross u v y x hu hv (p.symm hxy) hay (Or.inr ⟨hyu,hx.1,hx.2⟩)
    · have hvy : v < y := by omega
      exact noCross u v x y hu hv hxy hax (Or.inl ⟨hx.1,hx.2,hvy⟩)
  · apply ncConnected_no_saturated_interval p hc (fun x => lo ≤ x ∧ x ≤ hi)
      (by intros; omega) ?_ a b (bounds a (p.refl a)) hbmid
    intro x y hxy hx
    by_contra hy
    have hax : ¬ p a x := fun h => hy (bounds y (p.trans h hxy))
    have hay : ¬ p a y := fun h => hax (p.trans h (p.symm hxy))
    have hneL : lo ≠ x := fun h => hax (h ▸ hlo)
    have hneH : x ≠ hi := fun h => hax (h.symm ▸ hhi)
    have hlx : lo < x := by omega
    have hxh : x < hi := by omega
    by_cases hyl : y < lo
    · exact noCross lo hi y x hlo hhi (p.symm hxy) hay (Or.inr ⟨hyl,hlx,hxh⟩)
    · have hhy : hi < y := by omega
      exact noCross lo hi x y hlo hhi hxy hax (Or.inl ⟨hlx,hxh,hhy⟩)

#print axioms ncConnected_every_class_crossed
end LC004

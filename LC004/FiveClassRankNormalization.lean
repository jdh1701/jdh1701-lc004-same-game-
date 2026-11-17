import LC004.FiveClassGeometryApplication

namespace LC004

/-- Extend a finite increasing sequence by consecutive points after its last
entry. This constructs the normal form needed by the finite geometry theorem. -/
def extendFiniteIncreasing {n : Nat} (p : Fin (n+1) → Nat) (k : Nat) : Nat :=
  if h : k < n+1 then p ⟨k,h⟩ else p ⟨n, by omega⟩ + (k-n)

theorem extendFiniteIncreasing_eq {n : Nat} (p : Fin (n+1) → Nat)
    (i : Fin (n+1)) : extendFiniteIncreasing p i.val = p i := by
  simp [extendFiniteIncreasing, i.isLt]

theorem extendFiniteIncreasing_strictMono {n : Nat} (p : Fin (n+1) → Nat)
    (hp : StrictMono p) : StrictMono (extendFiniteIncreasing p) := by
  intro u v huv
  unfold extendFiniteIncreasing
  split_ifs with hu hv hv
  · exact hp (show (⟨u, hu⟩ : Fin (n+1)) < ⟨v, hv⟩ from huv)
  · have hle := hp.monotone (show (⟨u, hu⟩ : Fin (n+1)) ≤ ⟨n, by omega⟩ from by
      change u ≤ n
      omega)
    omega
  · omega
  · omega

/-- Every finite set of ten actual positions is exactly the increasing image
of the ten ranks, with an explicit extension to the whole natural line. -/
theorem ten_positions_parametrization (s : Finset Nat) (hs : s.card = 10) :
    ∃ f : Nat → Nat, StrictMono f ∧
      ∀ x, x ∈ (List.range 10).map f ↔ x ∈ s := by
  let p := s.orderEmbOfFin hs
  let f := extendFiniteIncreasing p
  refine ⟨f, extendFiniteIncreasing_strictMono p p.strictMono, ?_⟩
  intro x
  constructor
  · rintro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i < 10 := List.mem_range.mp hi
    have he : f i = p ⟨i, hi'⟩ := extendFiniteIncreasing_eq p ⟨i, hi'⟩
    rw [he]
    exact s.orderEmbOfFin_mem hs _
  · intro hx
    obtain ⟨i, hi⟩ := (s.orderIsoOfFin hs).surjective ⟨x,hx⟩
    refine List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
    rw [show f i.val = p i from extendFiniteIncreasing_eq p i]
    exact congrArg Subtype.val hi

/-- Splitting a ten-point increasing sequence by membership in either of two
classes gives their canonical sorted position lists. -/
theorem five_classes_rank_normal_form (G H : Finset Nat)
    (hG : G.card = 5) (hH : H.card = 5) (hd : Disjoint G H) :
    ∃ f : Nat → Nat, ∃ g : List Nat,
      StrictMono f ∧ g ∈ (List.range 10).sublistsLen 5 ∧
      g.map f = G.sort (· ≤ ·) ∧
      (fiveOtherRanks g).map f = H.sort (· ≤ ·) := by
  have hs : (G ∪ H).card = 10 := by rw [Finset.card_union_of_disjoint hd, hG, hH]
  obtain ⟨f, hf, himage⟩ := ten_positions_parametrization (G ∪ H) hs
  let g := (List.range 10).filter (fun i => decide (f i ∈ G))
  have hgmem (i : Nat) : i ∈ g ↔ i < 10 ∧ f i ∈ G := by
    simp [g]
  have hsorted : g.Sorted (· < ·) := (List.sorted_lt_range 10).filter _
  have hgm : g.map f = G.sort (· ≤ ·) := by
    apply List.Sorted.eq_of_mem_iff (hsorted.map f (fun _ _ h => hf h)) G.sort_sorted_lt
    intro x
    rw [Finset.mem_sort]
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact (hgmem i).mp hi |>.2
    · intro hx
      obtain ⟨i, hi, hix⟩ := List.mem_map.mp ((himage x).mpr (Finset.mem_union_left H hx))
      exact List.mem_map.mpr ⟨i, (hgmem i).mpr ⟨List.mem_range.mp hi, hix ▸ hx⟩, hix⟩
  have hglen : g.length = 5 := by
    have hl := congrArg List.length hgm
    simpa [hG] using hl
  have hgrank : g ∈ (List.range 10).sublistsLen 5 := by
    have hm := List.mem_sublistsLen_self (show List.Sublist g (List.range 10) from List.filter_sublist)
    simpa only [hglen] using hm
  have hother : (fiveOtherRanks g).map f = H.sort (· ≤ ·) := by
    have ho : (fiveOtherRanks g).Sorted (· < ·) := (List.sorted_lt_range 10).filter _
    apply List.Sorted.eq_of_mem_iff (ho.map f (fun _ _ h => hf h)) H.sort_sorted_lt
    intro x
    rw [Finset.mem_sort]
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi' : i < 10 ∧ i ∉ g := by simpa [fiveOtherRanks] using hi
      have hnot : f i ∉ G := fun h => hi'.2 ((hgmem i).mpr ⟨hi'.1,h⟩)
      have hu := (himage (f i)).mp (List.mem_map.mpr ⟨i,List.mem_range.mpr hi'.1,rfl⟩)
      exact (Finset.mem_union.mp hu).resolve_left hnot
    · intro hx
      obtain ⟨i, hi, hix⟩ := List.mem_map.mp ((himage x).mpr (Finset.mem_union_right G hx))
      have hnot : i ∉ g := by
        intro hig
        have hxG : x ∈ G := hix ▸ ((hgmem i).mp hig).2
        exact Finset.disjoint_left.mp hd hxG hx
      exact List.mem_map.mpr ⟨i, by simpa [fiveOtherRanks] using And.intro hi hnot, hix⟩
  exact ⟨f,g,hf,hgrank,hgm,hother⟩

#print axioms five_classes_rank_normal_form
end LC004

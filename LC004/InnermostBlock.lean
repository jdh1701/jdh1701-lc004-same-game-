import LC004.HistoryCertificate

namespace LC004

/-- Distinct blocks in an exact-once list partition are disjoint. -/
theorem disjoint_blocks_of_nodup_flatten {α : Type*}
    {blocks : List (List α)} (h : blocks.flatten.Nodup)
    {b c : List α} (hb : b ∈ blocks) (hc : c ∈ blocks) (hne : b ≠ c) :
    List.Disjoint b c := by
  induction blocks with
  | nil => simp at hb
  | cons d ds ih =>
      have hd := List.nodup_append.mp h
      simp only [List.mem_cons] at hb hc
      rw [List.disjoint_left]
      intro p hp hpc
      rcases hb with rfl | hb
      · rcases hc with rfl | hc
        · exact hne rfl
        · exact (List.disjoint_left.mp hd.2.2) p hp
            (List.mem_flatten.mpr ⟨c, hc, hpc⟩)
      · rcases hc with rfl | hc
        · exact (List.disjoint_left.mp hd.2.2) p hpc
            (List.mem_flatten.mpr ⟨b, hb, hp⟩)
        · exact (List.disjoint_left.mp (ih hd.2.1 hb hc hne)) p hp hpc

theorem Noncrossing23Certificate.flatten_nodup {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color) :
    cert.blocks.flatten.Nodup :=
  cert.exactCover.nodup_iff.mpr (List.nodup_finRange n)

theorem Noncrossing23Certificate.cover_position {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    (p : Fin n) : ∃ b ∈ cert.blocks, p ∈ b := by
  exact List.mem_flatten.mp
    (cert.exactCover.mem_iff.mpr (List.mem_finRange p))

/-- A nonempty finite block has attained lower and upper endpoints. -/
theorem fin_block_extrema {n : Nat} (b : List (Fin n))
    (h : 0 < b.length) :
    ∃ lo ∈ b, ∃ hi ∈ b,
      ∀ p ∈ b, lo.val ≤ p.val ∧ p.val ≤ hi.val := by
  classical
  obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos h
  have hne : b.toFinset.Nonempty := ⟨p, List.mem_toFinset.mpr hp⟩
  refine ⟨b.toFinset.min' hne,
    List.mem_toFinset.mp (Finset.min'_mem _ _),
    b.toFinset.max' hne,
    List.mem_toFinset.mp (Finset.max'_mem _ _), ?_⟩
  intro x hx
  exact ⟨Finset.min'_le _ x (List.mem_toFinset.mpr hx),
    Finset.le_max' _ x (List.mem_toFinset.mpr hx)⟩

theorem Noncrossing23Certificate.no_alternation {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    {b c : List (Fin n)} (hb : b ∈ cert.blocks) (hc : c ∈ cert.blocks)
    {u v s t : Fin n} (hu : u ∈ b) (hv : v ∈ b)
    (hs : s ∈ c) (ht : t ∈ c) :
    ¬ PairCross u.val v.val s.val t.val := by
  intro hcross
  exact cert.noncrossing (b.map Fin.val)
    (List.mem_map.mpr ⟨b, hb, rfl⟩) (c.map Fin.val)
    (List.mem_map.mpr ⟨c, hc, rfl⟩)
    ⟨u.val, List.mem_map.mpr ⟨u, hu, rfl⟩,
     v.val, List.mem_map.mpr ⟨v, hv, rfl⟩,
     s.val, List.mem_map.mpr ⟨s, hs, rfl⟩,
     t.val, List.mem_map.mpr ⟨t, ht, rfl⟩, hcross⟩

/-- A nonempty complete noncrossing certificate contains an interval
block: every position between its attained endpoints belongs to it.
No hypothesis about the order of positions or blocks in their lists
is needed. -/
theorem Noncrossing23Certificate.exists_innermost_block {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    (hn : 0 < n) :
    ∃ b ∈ cert.blocks, ∃ lo hi : Fin n,
      lo ∈ b ∧ hi ∈ b ∧
      ∀ p : Fin n, p ∈ b ↔ lo.val ≤ p.val ∧ p.val ≤ hi.val := by
  classical
  let P : Nat → Prop := fun d =>
    ∃ b ∈ cert.blocks, ∃ lo ∈ b, ∃ hi ∈ b,
      hi.val - lo.val = d ∧
      ∀ p ∈ b, lo.val ≤ p.val ∧ p.val ≤ hi.val
  have hex : ∃ d, P d := by
    obtain ⟨b, hb, hp⟩ := cert.cover_position ⟨0, hn⟩
    obtain ⟨lo, hlo, hi, hhi, hbounds⟩ :=
      fin_block_extrema b (List.length_pos_of_mem hp)
    exact ⟨hi.val - lo.val, b, hb, lo, hlo, hi, hhi, rfl, hbounds⟩
  obtain ⟨b, hb, lo, hlo, hi, hhi, hspan, hbounds⟩ := Nat.find_spec hex
  refine ⟨b, hb, lo, hi, hlo, hhi, ?_⟩
  intro p
  refine ⟨fun hp => hbounds p hp, ?_⟩
  intro hpBounds
  by_contra hpNot
  obtain ⟨c, hc, hpc⟩ := cert.cover_position p
  have hbc : b ≠ c := by
    intro heq
    exact hpNot (heq.symm ▸ hpc)
  have hdisjoint := disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hc hbc
  have hplNe : p.val ≠ lo.val := by
    intro heq
    exact hpNot ((Fin.ext heq).symm ▸ hlo)
  have hphNe : p.val ≠ hi.val := by
    intro heq
    exact hpNot ((Fin.ext heq).symm ▸ hhi)
  have hpl : lo.val < p.val := by omega
  have hph : p.val < hi.val := by omega
  have hcInside : ∀ t ∈ c, lo.val < t.val ∧ t.val < hi.val := by
    intro t ht
    have htlNe : t.val ≠ lo.val := by
      intro heq
      exact (List.disjoint_left.mp hdisjoint) lo hlo ((Fin.ext heq) ▸ ht)
    have hthNe : t.val ≠ hi.val := by
      intro heq
      exact (List.disjoint_left.mp hdisjoint) hi hhi ((Fin.ext heq) ▸ ht)
    constructor
    · by_contra hle
      have hlt : t.val < lo.val := by omega
      exact cert.no_alternation hb hc hlo hhi ht hpc (Or.inr ⟨hlt, hpl, hph⟩)
    · by_contra hge
      have hgt : hi.val < t.val := by omega
      exact cert.no_alternation hb hc hlo hhi hpc ht (Or.inl ⟨hpl, hph, hgt⟩)
  obtain ⟨clo, hclo, chi, hchi, hcbounds⟩ :=
    fin_block_extrema c (List.length_pos_of_mem hpc)
  have hcLo := hcInside clo hclo
  have hcHi := hcInside chi hchi
  have hcOrder := hcbounds clo hclo
  have hsmall : P (chi.val - clo.val) :=
    ⟨c, hc, clo, hclo, chi, hchi, rfl, hcbounds⟩
  have hminimal := Nat.find_min' hex hsmall
  omega

/-- In particular, the innermost block is an actual contiguous
monochromatic pair or triple of positions in the original word. -/
theorem Noncrossing23Certificate.exists_contiguous_monochromatic_block
    {n q : Nat} {color : Fin n → Fin q}
    (cert : Noncrossing23Certificate color) (hn : 0 < n) :
    ∃ b ∈ cert.blocks, ∃ gap k : Nat,
      (k = 2 ∨ k = 3) ∧ gap + k ≤ n ∧
      (∀ p : Fin n, p ∈ b ↔ gap ≤ p.val ∧ p.val < gap + k) ∧
      ∃ a : Fin q, ∀ p ∈ b, color p = a := by
  classical
  obtain ⟨b, hb, lo, hi, hlo, hhi, hmem⟩ := cert.exists_innermost_block hn
  have hnodup := (List.nodup_flatten.mp cert.flatten_nodup).1 b hb
  have hset : b.toFinset = Finset.Icc lo hi := by
    ext p
    simp only [List.mem_toFinset, Finset.mem_Icc]
    exact hmem p
  have hlen : b.length = hi.val + 1 - lo.val := by
    calc
      b.length = b.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ = hi.val + 1 - lo.val := by rw [hset, Fin.card_Icc]
  have hlohi := (hmem lo).mp hlo
  have hend : lo.val + b.length = hi.val + 1 := by omega
  have hbound := hi.isLt
  refine ⟨b, hb, lo.val, b.length, cert.sizes b hb, ?_, ?_,
    cert.monochromatic b hb⟩
  · omega
  · intro p
    rw [hmem]
    omega

#print axioms Noncrossing23Certificate.exists_innermost_block
#print axioms Noncrossing23Certificate.exists_contiguous_monochromatic_block

end LC004

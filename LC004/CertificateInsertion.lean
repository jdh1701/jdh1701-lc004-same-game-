import LC004.TypedInsertionPositions

namespace LC004

/-- Fresh and shifted old positions enumerate the new word exactly once. -/
theorem insertion_positions_perm {n : Nat} (gap k : Nat)
    (hgap : gap ≤ n) :
    (((List.finRange k).map (freshPosition gap k hgap)) ++
      ((List.finRange n).map (oldPosition gap k))).Perm
      (List.finRange (n + k)) := by
  have hdisjoint : List.Disjoint
      ((List.finRange k).map (freshPosition gap k hgap))
      ((List.finRange n).map (oldPosition gap k)) := by
    rw [List.disjoint_left]
    intro j hf ho
    obtain ⟨s, _, hs⟩ := List.mem_map.mp hf
    obtain ⟨i, _, hi⟩ := List.mem_map.mp ho
    exact oldPosition_ne_freshPosition gap k hgap i s (hi.trans hs.symm)
  have hnodup := ((List.nodup_finRange k).map
    (freshPosition_injective gap k hgap)).append
    ((List.nodup_finRange n).map (oldPosition_injective gap k)) hdisjoint
  apply (List.perm_ext_iff_of_nodup hnodup
    (List.nodup_finRange (n + k))).mpr
  intro j
  constructor
  · intro _
    exact List.mem_finRange j
  · intro _
    rcases insertion_positions_cover gap k hgap j with ⟨i, hi⟩ | ⟨s, hs⟩
    · exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨i, List.mem_finRange i, hi⟩))
    · exact List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨s, List.mem_finRange s, hs⟩))

/-- Insert one monochromatic pair/triple into a complete certificate.
The two color equations explicitly specify how the enlarged word
agrees with the old word and with the color of the inserted cells. -/
def Noncrossing23Certificate.insert {n q : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    (gap k : Nat) (hgap : gap ≤ n) (hk : k = 2 ∨ k = 3)
    (color' : Fin (n + k) → Fin q) (a : Fin q)
    (hold : ∀ i, color' (oldPosition gap k i) = color i)
    (hfresh : ∀ s, color' (freshPosition gap k hgap s) = a) :
    Noncrossing23Certificate color' where
  blocks := ((List.finRange k).map (freshPosition gap k hgap)) ::
    cert.blocks.map (List.map (oldPosition gap k))
  sizes := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simpa using hk
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      simpa using cert.sizes b0 hb0
  exactCover := by
    have hp : (cert.blocks.map (List.map (oldPosition gap k))).flatten.Perm
        ((List.finRange n).map (oldPosition gap k)) := by
      rw [← List.map_flatten]
      exact cert.exactCover.map (oldPosition gap k)
    exact (hp.append_left _).trans (insertion_positions_perm gap k hgap)
  monochromatic := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨a, ?_⟩
      intro p hp
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hp
      exact hfresh s
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      obtain ⟨c, hc⟩ := cert.monochromatic b0 hb0
      refine ⟨c, ?_⟩
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      exact (hold i).trans (hc i hi)
  noncrossing := by
    have hnew : ((List.finRange k).map
        (freshPosition gap k hgap)).map Fin.val =
        (List.range k).map (fun s => gap + s) := by
      calc
        _ = ((List.finRange k).map Fin.val).map (fun s => gap + s) := by
          simp [List.map_map, freshPosition, Function.comp_def]
        _ = _ := by rw [List.map_coe_finRange]
    have holdBlock (b : List (Fin n)) :
        (b.map (oldPosition gap k)).map Fin.val =
        shiftBlock gap k (b.map Fin.val) := by
      simp [List.map_map, shiftBlock, oldPosition, Function.comp_def]
    change NoncrossingBlockFamily
      ((((List.finRange k).map (freshPosition gap k hgap)).map Fin.val) ::
        (cert.blocks.map (List.map (oldPosition gap k))).map (List.map Fin.val))
    rw [hnew]
    simp only [List.map_map, Function.comp_def]
    simp_rw [holdBlock]
    have hbound : k ≤ 3 := by omega
    simpa only [List.map_map, Function.comp_def] using
      noncrossing_block_family_insert
        (cert.blocks.map (List.map Fin.val)) gap k hbound cert.noncrossing

#print axioms insertion_positions_perm
#print axioms Noncrossing23Certificate.insert

end LC004

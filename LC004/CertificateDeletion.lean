import LC004.CertificateFirstErase

namespace LC004

/-- A total contraction used only on surviving positions. The modulo
keeps it bounded even on deleted positions, which never occur in the
residual blocks. The empty residual word is handled separately. -/
def contractPosition {n : Nat} (gap k : Nat) (hn : 0 < n)
    (p : Fin (n + k)) : Fin n :=
  ⟨(if p.val < gap then p.val else p.val - k) % n, Nat.mod_lt _ hn⟩

theorem contractPosition_old {n : Nat} (gap k : Nat) (hn : 0 < n)
    (i : Fin n) :
    contractPosition gap k hn (oldPosition gap k i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases hg : i.val < gap
  · simp [contractPosition, oldPosition, shiftAfterInsertion, hg,
      Nat.mod_eq_of_lt hi]
  · have hafter : ¬ i.val + k < gap := by omega
    simp [contractPosition, oldPosition, shiftAfterInsertion, hg, hafter,
      Nat.mod_eq_of_lt hi]

theorem oldPosition_contract {n : Nat} (gap k : Nat) (hn : 0 < n)
    (hgap : gap ≤ n) (p : Fin (n + k))
    (hout : p.val < gap ∨ gap + k ≤ p.val) :
    oldPosition gap k (contractPosition gap k hn p) = p := by
  apply Fin.ext
  have hp := p.isLt
  rcases hout with hleft | hright
  · have hpn : p.val < n := by omega
    simp [contractPosition, oldPosition, shiftAfterInsertion, hleft,
      Nat.mod_eq_of_lt hpn]
  · have hnot : ¬ p.val < gap := by omega
    have hpn : p.val - k < n := by omega
    have hafter : ¬ p.val - k < gap := by omega
    have hcancel : p.val - k + k = p.val := by omega
    simp [contractPosition, oldPosition, shiftAfterInsertion, hnot, hafter,
      Nat.mod_eq_of_lt hpn, hcancel]

/-- Delete a block occupying exactly the interval [gap,gap+k), and
contract every surviving block. All complete-certificate invariants
are preserved. This theorem concerns a positive residual length. -/
noncomputable def Noncrossing23Certificate.deleteInterval
    {n q k : Nat} {color : Fin (n + k) → Fin q}
    (cert : Noncrossing23Certificate color)
    (gap : Nat) (hn : 0 < n) (hgap : gap ≤ n)
    (b : List (Fin (n + k))) (hb : b ∈ cert.blocks)
    (hinterval : ∀ p, p ∈ b ↔ gap ≤ p.val ∧ p.val < gap + k)
    (color' : Fin n → Fin q)
    (hcolor : ∀ i, color (oldPosition gap k i) = color' i) :
    Noncrossing23Certificate color' := by
  classical
  let rest := cert.blocks.filter (fun c => decide (c ≠ b))
  let shrink := contractPosition gap k hn
  have hrest (c : List (Fin (n + k))) :
      c ∈ rest ↔ c ∈ cert.blocks ∧ c ≠ b := by simp [rest]
  have houtside : ∀ c ∈ rest, ∀ p ∈ c,
      p.val < gap ∨ gap + k ≤ p.val := by
    intro c hc p hp
    obtain ⟨hcOrig, hcNe⟩ := (hrest c).mp hc
    have hdis := disjoint_blocks_of_nodup_flatten cert.flatten_nodup hb hcOrig
      (fun heq => hcNe heq.symm)
    by_cases hleft : p.val < gap
    · exact Or.inl hleft
    · right
      by_contra hright
      have hpb := (hinterval p).mpr ⟨by omega, by omega⟩
      exact (List.disjoint_left.mp hdis) hpb hp
  have hback : ∀ c ∈ rest, ∀ p ∈ c,
      oldPosition gap k (shrink p) = p := by
    intro c hc p hp
    exact oldPosition_contract gap k hn hgap p (houtside c hc p hp)
  have hflatBack : (rest.flatten.map shrink).map (oldPosition gap k) =
      rest.flatten := by
    rw [List.map_map]
    calc
      _ = rest.flatten.map id := by
        apply List.map_congr_left
        intro p hp
        obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hp
        exact hback c hc p hpc
      _ = _ := List.map_id _
  have hflatNodup : rest.flatten.Nodup :=
    cert.flatten_nodup.sublist (List.filter_sublist.flatten)
  have hshrinkNodup : (rest.flatten.map shrink).Nodup := by
    apply List.Nodup.of_map (oldPosition gap k)
    rw [hflatBack]
    exact hflatNodup
  have hcover : (rest.flatten.map shrink).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hshrinkNodup (List.nodup_finRange n)).mpr
    intro i
    refine ⟨fun _ => List.mem_finRange i, fun _ => ?_⟩
    obtain ⟨c, hc, hpc⟩ := cert.cover_position (oldPosition gap k i)
    have hnotb : c ≠ b := by
      intro heq
      have hpb : oldPosition gap k i ∈ b := heq ▸ hpc
      have hinside := (hinterval _).mp hpb
      have hout : (oldPosition gap k i).val < gap ∨
          gap + k ≤ (oldPosition gap k i).val := by
        unfold oldPosition shiftAfterInsertion
        split_ifs <;> simp_all <;> omega
      omega
    exact List.mem_map.mpr ⟨oldPosition gap k i,
      List.mem_flatten.mpr ⟨c, (hrest c).mpr ⟨hc, hnotb⟩, hpc⟩,
      contractPosition_old gap k hn i⟩
  refine {
    blocks := rest.map (List.map shrink)
    sizes := ?_
    exactCover := ?_
    monochromatic := ?_
    noncrossing := ?_ }
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    simpa using cert.sizes c0 ((hrest c0).mp hc0).1
  · rw [← List.map_flatten]
    exact hcover
  · intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    obtain ⟨a, ha⟩ := cert.monochromatic c0 ((hrest c0).mp hc0).1
    refine ⟨a, ?_⟩
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
    have heq := hcolor (shrink p)
    rw [hback c0 hc0 p hp] at heq
    exact heq.symm.trans (ha p hp)
  · have hshift : ∀ c ∈ rest,
        shiftBlock gap k ((c.map shrink).map Fin.val) = c.map Fin.val := by
      intro c hc
      unfold shiftBlock
      simp only [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact congrArg Fin.val (hback c hc p hp)
    have hfamily : NoncrossingBlockFamily
        (rest.map (fun c => (c.map shrink).map Fin.val)) := by
      intro a ha d hd hcross
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      have hcrossOld := (blocksCross_shift_iff gap k
        ((c.map shrink).map Fin.val) ((e.map shrink).map Fin.val)).mpr hcross
      rw [hshift c hc, hshift e he] at hcrossOld
      exact cert.noncrossing (c.map Fin.val)
        (List.mem_map.mpr ⟨c, ((hrest c).mp hc).1, rfl⟩)
        (e.map Fin.val) (List.mem_map.mpr ⟨e, ((hrest e).mp he).1, rfl⟩) hcrossOld
    simpa only [List.map_map, Function.comp_def] using hfamily

#print axioms Noncrossing23Certificate.deleteInterval

/-- A length equality lets clients retain their original position type. -/
theorem delete_interval_of_length {N n q k : Nat} (hlen : N = n + k)
    {color : Fin N → Fin q} (cert : Noncrossing23Certificate color)
    (gap : Nat) (hn : 0 < n) (hgap : gap ≤ n)
    (b : List (Fin N)) (hb : b ∈ cert.blocks)
    (hinterval : ∀ p, p ∈ b ↔ gap ≤ p.val ∧ p.val < gap + k)
    (color' : Fin n → Fin q)
    (hcolor : ∀ i, color (Fin.cast hlen.symm (oldPosition gap k i)) = color' i) :
    Nonempty (Noncrossing23Certificate color') := by
  subst N
  exact ⟨cert.deleteInterval gap hn hgap b hb hinterval color' hcolor⟩

end LC004

import LC004.FiveCoefficientChoiceBridge
import LC004.FiveClassSurvivorRecognition

namespace LC004
open scoped Classical

def fiveRankBlocks (s : Fin 10) : List (List (Fin 5)) :=
  [(List.finRange 5).filter (fiveSplitBit s),
   (List.finRange 5).filter (fun u => !(fiveSplitBit s u))]

theorem fiveRankBlocks_relation : ∀ s : Fin 10, ∀ u v : Fin 5,
    (fiveSplitBit s u = fiveSplitBit s v) ↔
      ∃ B ∈ fiveRankBlocks s, u ∈ B ∧ v ∈ B := by decide +kernel

/-- Parametric list identity: the finite label operations commute with any
placement of the five ranks, without assuming order or injectivity. -/
theorem fiveRankBlocks_map (f : Fin 5 → Nat) (s : Fin 10) :
    (fiveRankBlocks s).map (List.map f) =
      fiveSplitBlocks ((List.finRange 5).map f) s := by
  fin_cases s <;> rfl

def fivePositionBlocks {n k : Nat} (e : Fin n ≃ Fin k × Fin 5)
    (a : Fin k → Fin 10) : List (List (Fin n)) :=
  (List.finRange k).flatMap fun i =>
    (fiveRankBlocks (a i)).map (fun B => B.map (fun u => e.symm (i,u)))

theorem fivePositionBlocks_relation {n k : Nat} (e : Fin n ≃ Fin k × Fin 5)
    (a : Fin k → Fin 10) (x y : Fin n) :
    Setoid.comap e (fiveAssignmentSetoid a) x y ↔
      ∃ B ∈ fivePositionBlocks e a, x ∈ B ∧ y ∈ B := by
  obtain ⟨⟨i,u⟩,rfl⟩ := e.symm.surjective x
  obtain ⟨⟨j,v⟩,rfl⟩ := e.symm.surjective y
  constructor
  · intro h
    have hh : (i,fiveSplitBit (a i) u) = (j,fiveSplitBit (a j) v) := by
      simpa only [Setoid.comap_rel,fiveAssignmentSetoid,Setoid.ker_def,e.apply_symm_apply] using h
    have hij : i = j := congrArg Prod.fst hh
    subst j
    obtain ⟨B,hB,hu,hv⟩ := (fiveRankBlocks_relation (a i) u v).mp (congrArg Prod.snd hh)
    refine ⟨B.map (fun r => e.symm (i,r)),?_,?_,?_⟩
    · exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,List.mem_map.mpr ⟨B,hB,rfl⟩⟩
    · exact List.mem_map.mpr ⟨u,hu,rfl⟩
    · exact List.mem_map.mpr ⟨v,hv,rfl⟩
  · rintro ⟨B,hB,hx,hy⟩
    obtain ⟨l,_,hBl⟩ := List.mem_flatMap.mp hB
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hBl
    obtain ⟨r,hr,her⟩ := List.mem_map.mp hx
    obtain ⟨s,hs,hes⟩ := List.mem_map.mp hy
    have hi : l = i := congrArg Prod.fst (e.symm.injective her)
    have hj : l = j := congrArg Prod.fst (e.symm.injective hes)
    subst l
    subst j
    have hru : r = u := congrArg Prod.snd (e.symm.injective her)
    have hsv : s = v := congrArg Prod.snd (e.symm.injective hes)
    subst r
    subst s
    have hb := (fiveRankBlocks_relation (a i) u v).mpr ⟨R,hR,hr,hs⟩
    have hh : (i,fiveSplitBit (a i) u) = (i,fiveSplitBit (a i) v) := Prod.ext rfl hb
    simpa only [Setoid.comap_rel,fiveAssignmentSetoid,Setoid.ker_def,e.apply_symm_apply] using hh

/-- The noncrossing predicate used by original CertificateConstraint is exactly
the selected block-family predicate, not an assumed analogous condition. -/
theorem fivePositionBlocks_noncrossing_iff {n k : Nat} (e : Fin n ≃ Fin k × Fin 5)
    (a : Fin k → Fin 10) :
    PatternNoncrossing (Setoid.comap e (fiveAssignmentSetoid a)) ↔
      NoncrossingBlockFamily ((fivePositionBlocks e a).map (List.map Fin.val)) := by
  let c := Setoid.comap e (fiveAssignmentSetoid a)
  have hrel := fivePositionBlocks_relation e a
  constructor
  · intro hnc
    have hsmall := five_encoded_small_classes e a
    have hno : PatternNoAlternation c := small_noncrossing_no_alternation c (fun x => by
      have h := hsmall x
      change (setoidClassFinset c x).card = 2 ∨ (setoidClassFinset c x).card = 3 at h
      change (patternClassPositions c x).card ≤ 3
      simpa only [setoidClassFinset,patternClassPositions] using (show (setoidClassFinset c x).card ≤ 3 from by omega)) hnc
    intro B hB C hC hcross
    obtain ⟨B,hB0,rfl⟩ := List.mem_map.mp hB
    obtain ⟨C,hC0,rfl⟩ := List.mem_map.mp hC
    obtain ⟨u,hu,v,hv,x,hx,y,hy,hcross⟩ := hcross
    obtain ⟨u,hu0,rfl⟩ := List.mem_map.mp hu
    obtain ⟨v,hv0,rfl⟩ := List.mem_map.mp hv
    obtain ⟨x,hx0,rfl⟩ := List.mem_map.mp hx
    obtain ⟨y,hy0,rfl⟩ := List.mem_map.mp hy
    have huv : c u v := (hrel u v).mpr ⟨B,hB0,hu0,hv0⟩
    have hxy : c x y := (hrel x y).mpr ⟨C,hC0,hx0,hy0⟩
    rcases hcross with h | h
    · exact hno u x v y h.1 h.2.1 h.2.2 ⟨huv,hxy⟩
    · exact hno x u y v h.1 h.2.1 h.2.2 ⟨hxy,huv⟩
  · intro hnc
    apply no_alternation_noncrossing
    intro u x v y hux hxv hvy huvxy
    obtain ⟨B,hB,hu,hv⟩ := (hrel u v).mp huvxy.1
    obtain ⟨C,hC,hx,hy⟩ := (hrel x y).mp huvxy.2
    apply hnc (B.map Fin.val) (List.mem_map.mpr ⟨B,hB,rfl⟩)
      (C.map Fin.val) (List.mem_map.mpr ⟨C,hC,rfl⟩)
    exact ⟨u.val,List.mem_map.mpr ⟨u,hu,rfl⟩,v.val,List.mem_map.mpr ⟨v,hv,rfl⟩,
      x.val,List.mem_map.mpr ⟨x,hx,rfl⟩,y.val,List.mem_map.mpr ⟨y,hy,rfl⟩,
      Or.inl ⟨hux,hxv,hvy⟩⟩

#print axioms fivePositionBlocks_noncrossing_iff
end LC004

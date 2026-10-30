import LC004.WinningConstraintGenerators
import LC004.NoncrossingClosureRegions

namespace LC004

/-- Canonical restricted representatives reduce six-point checking from 46,656
arbitrary colorings to 720 bounded representative functions. -/
abbrev BoundedClassCode (n : Nat) := (i : Fin n) → Fin (i.val + 1)

def boundedClassColor {n : Nat} (f : BoundedClassCode n) (i : Fin n) : Fin n :=
  ⟨(f i).val,lt_of_le_of_lt (Nat.lt_succ_iff.mp (f i).isLt) i.isLt⟩

def SmallColor23 {n : Nat} (f : Fin n → Fin n) : Prop :=
  ∀ u, (Finset.univ.filter (fun v => f u = f v)).card = 2 ∨
    (Finset.univ.filter (fun v => f u = f v)).card = 3

def NoncrossingColor {n : Nat} (f : Fin n → Fin n) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → f a = f c → f b = f d → f a = f b

noncomputable def leastClassPosition {n : Nat} (p : ColorPattern n) (i : Fin n) : Fin n :=
  (patternClassPositions p i).min' ⟨i,by simpa only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and] using p.refl i⟩

theorem leastClassPosition_mem {n : Nat} (p : ColorPattern n) (i : Fin n) :
    p i (leastClassPosition p i) := by
  have h := Finset.min'_mem (patternClassPositions p i) ⟨i,by simpa only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and] using p.refl i⟩
  simpa only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and] using h

theorem leastClassPosition_le {n : Nat} (p : ColorPattern n) (i : Fin n) :
    leastClassPosition p i ≤ i := by
  apply Finset.min'_le
  simpa only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and] using p.refl i

theorem leastClassPosition_eq_iff {n : Nat} (p : ColorPattern n) (i j : Fin n) :
    leastClassPosition p i = leastClassPosition p j ↔ p i j := by
  constructor
  · intro h
    have hi := leastClassPosition_mem p i
    have hj := leastClassPosition_mem p j
    rw [h] at hi
    exact p.trans hi (p.symm hj)
  · intro hij
    have he : patternClassPositions p i = patternClassPositions p j := by
      ext x
      simp only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h => p.trans (p.symm hij) h,fun h => p.trans hij h⟩
    simp only [leastClassPosition,he]

noncomputable def patternBoundedCode {n : Nat} (p : ColorPattern n) : BoundedClassCode n :=
  fun i => ⟨(leastClassPosition p i).val,Nat.lt_succ_iff.mpr (leastClassPosition_le p i)⟩

theorem patternBoundedColor_eq_iff {n : Nat} (p : ColorPattern n) (i j : Fin n) :
    boundedClassColor (patternBoundedCode p) i = boundedClassColor (patternBoundedCode p) j ↔ p i j :=
  leastClassPosition_eq_iff p i j

def localNC5Color : Fin 5 → Fin 5 → Fin 5 :=
  ![![0,0,0,1,1],
    ![0,0,1,1,0],
    ![0,0,1,1,1],
    ![0,1,1,0,0],
    ![0,1,1,1,0]]


def localNC6Color : Fin 8 → Fin 6 → Fin 6 :=
  ![![0,0,0,1,1,1],
    ![0,0,1,1,1,0],
    ![0,0,1,1,2,2],
    ![0,0,1,2,2,1],
    ![0,1,1,0,2,2],
    ![0,1,1,1,0,0],
    ![0,1,1,2,2,0],
    ![0,1,2,2,1,0]]

def bounded5Color (a1 : Fin 2) (a2 : Fin 3) (a3 : Fin 4) (a4 : Fin 5) : Fin 5 → Fin 5 :=
  ![0,Fin.castLE (by decide : 2 ≤ 5) a1,Fin.castLE (by decide : 3 ≤ 5) a2,Fin.castLE (by decide : 4 ≤ 5) a3,Fin.castLE (by decide : 5 ≤ 5) a4]

theorem localNC5_color_complete : ∀ (a1 : Fin 2) (a2 : Fin 3) (a3 : Fin 4) (a4 : Fin 5),
    SmallColor23 (bounded5Color a1 a2 a3 a4) → NoncrossingColor (bounded5Color a1 a2 a3 a4) → ∃ s : Fin 5,
      ∀ u v, (localNC5Color s u = localNC5Color s v ↔ bounded5Color a1 a2 a3 a4 u = bounded5Color a1 a2 a3 a4 v) := by
  unfold SmallColor23 NoncrossingColor
  decide +kernel

theorem localNC5_pattern_complete (p : ColorPattern 5)
    (hs : ∀ u, (patternClassPositions p u).card = 2 ∨
      (patternClassPositions p u).card = 3) (hnc : PatternNoncrossing p) :
    ∃ s : Fin 5, p = Setoid.ker (localNC5Color s) := by
  let f := patternBoundedCode p
  let g := bounded5Color (f 1) (f 2) (f 3) (f 4)
  have hg : g = boundedClassColor f := by
    funext i
    fin_cases i
    · apply Fin.ext
      have h := (f 0).isLt
      change 0 = (f 0).val
      omega
    all_goals rfl
  have hsize : SmallColor23 (boundedClassColor f) := by
    intro u
    have he : Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v) =
        patternClassPositions p u := by
      ext v
      simp only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and]
      exact patternBoundedColor_eq_iff p u v
    change (Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v)).card = 2 ∨
      (Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v)).card = 3
    rw [he]
    exact hs u
  have hcolor : NoncrossingColor (boundedClassColor f) := by
    intro a b c d hab hbc hcd hac hbd
    exact (patternBoundedColor_eq_iff p a b).mpr (hnc a b c d hab hbc hcd
      ((patternBoundedColor_eq_iff p a c).mp hac) ((patternBoundedColor_eq_iff p b d).mp hbd))
  have hsg : SmallColor23 g := hg.symm ▸ hsize
  have hng : NoncrossingColor g := hg.symm ▸ hcolor
  obtain ⟨s,he⟩ := localNC5_color_complete (f 1) (f 2) (f 3) (f 4) hsg hng
  change ∀ u v, (localNC5Color s u = localNC5Color s v ↔ g u = g v) at he
  rw [hg] at he
  refine ⟨s,Setoid.ext (fun u v => ?_)⟩
  exact (patternBoundedColor_eq_iff p u v).symm.trans (he u v).symm

def bounded6Color (a1 : Fin 2) (a2 : Fin 3) (a3 : Fin 4) (a4 : Fin 5) (a5 : Fin 6) : Fin 6 → Fin 6 :=
  ![0,Fin.castLE (by decide : 2 ≤ 6) a1,Fin.castLE (by decide : 3 ≤ 6) a2,Fin.castLE (by decide : 4 ≤ 6) a3,Fin.castLE (by decide : 5 ≤ 6) a4,Fin.castLE (by decide : 6 ≤ 6) a5]

theorem localNC6_color_complete : ∀ (a1 : Fin 2) (a2 : Fin 3) (a3 : Fin 4) (a4 : Fin 5) (a5 : Fin 6),
    SmallColor23 (bounded6Color a1 a2 a3 a4 a5) → NoncrossingColor (bounded6Color a1 a2 a3 a4 a5) → ∃ s : Fin 8,
      ∀ u v, (localNC6Color s u = localNC6Color s v ↔ bounded6Color a1 a2 a3 a4 a5 u = bounded6Color a1 a2 a3 a4 a5 v) := by
  unfold SmallColor23 NoncrossingColor
  decide +kernel

theorem localNC6_pattern_complete (p : ColorPattern 6)
    (hs : ∀ u, (patternClassPositions p u).card = 2 ∨
      (patternClassPositions p u).card = 3) (hnc : PatternNoncrossing p) :
    ∃ s : Fin 8, p = Setoid.ker (localNC6Color s) := by
  let f := patternBoundedCode p
  let g := bounded6Color (f 1) (f 2) (f 3) (f 4) (f 5)
  have hg : g = boundedClassColor f := by
    funext i
    fin_cases i
    · apply Fin.ext
      have h := (f 0).isLt
      change 0 = (f 0).val
      omega
    all_goals rfl
  have hsize : SmallColor23 (boundedClassColor f) := by
    intro u
    have he : Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v) =
        patternClassPositions p u := by
      ext v
      simp only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and]
      exact patternBoundedColor_eq_iff p u v
    change (Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v)).card = 2 ∨
      (Finset.univ.filter (fun v => boundedClassColor f u = boundedClassColor f v)).card = 3
    rw [he]
    exact hs u
  have hcolor : NoncrossingColor (boundedClassColor f) := by
    intro a b c d hab hbc hcd hac hbd
    exact (patternBoundedColor_eq_iff p a b).mpr (hnc a b c d hab hbc hcd
      ((patternBoundedColor_eq_iff p a c).mp hac) ((patternBoundedColor_eq_iff p b d).mp hbd))
  have hsg : SmallColor23 g := hg.symm ▸ hsize
  have hng : NoncrossingColor g := hg.symm ▸ hcolor
  obtain ⟨s,he⟩ := localNC6_color_complete (f 1) (f 2) (f 3) (f 4) (f 5) hsg hng
  change ∀ u v, (localNC6Color s u = localNC6Color s v ↔ g u = g v) at he
  rw [hg] at he
  refine ⟨s,Setoid.ext (fun u v => ?_)⟩
  exact (patternBoundedColor_eq_iff p u v).symm.trans (he u v).symm

#print axioms localNC5_pattern_complete
#print axioms localNC6_pattern_complete
end LC004

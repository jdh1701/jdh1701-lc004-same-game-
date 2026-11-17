import LC004.FiveClassSplitJoins
import LC004.WinningConstraintGenerators

namespace LC004
open scoped Classical

/-- Exhaustive local arithmetic/classification check. The input is any coloring
of five points, including unused labels, rather than an assumed two-block split. -/
theorem five_small_coloring_split : ∀ color : Fin 5 → Fin 5,
    (∀ u : Fin 5,
      (Finset.univ.filter (fun v => color u = color v)).card = 2 ∨
      (Finset.univ.filter (fun v => color u = color v)).card = 3) →
    ∃ s : Fin 10, ∀ u v : Fin 5,
      (fiveSplitBit s u = fiveSplitBit s v ↔ color u = color v) := by
  decide +kernel

/-- Different pair choices give different partitions, not merely different
labels for the same two blocks. -/
theorem fiveLocalSplit_injective : Function.Injective fiveLocalSplit := by
  have hfin : ∀ s t : Fin 10,
      (∀ u v : Fin 5, (fiveSplitBit s u = fiveSplitBit s v ↔
        fiveSplitBit t u = fiveSplitBit t v)) → s = t := by decide +kernel
  intro s t he
  apply hfin s t
  intro u v
  change fiveLocalSplit s u v ↔ fiveLocalSplit t u v
  rw [he]

/-- Every pair/triple partition on five points has one unique local split label.
This is the inverse representation needed for original certificate generators. -/
theorem five_small_pattern_unique_split (p : ColorPattern 5)
    (hsmall : ∀ u, (patternClassPositions p u).card = 2 ∨
      (patternClassPositions p u).card = 3) :
    ∃! s : Fin 10, p = fiveLocalSplit s := by
  have hc : ∀ u : Fin 5,
      (Finset.univ.filter (fun v => patternColor p u = patternColor p v)).card = 2 ∨
      (Finset.univ.filter (fun v => patternColor p u = patternColor p v)).card = 3 := by
    intro u
    simpa only [patternClassPositions,patternColor_eq_iff] using hsmall u
  obtain ⟨s,hs⟩ := five_small_coloring_split (patternColor p) hc
  have he : p = fiveLocalSplit s := by
    apply Setoid.ext
    intro u v
    exact (patternColor_eq_iff p u v).symm.trans (hs u v).symm
  exact ⟨s,he,fun t ht => fiveLocalSplit_injective (ht.symm.trans he)⟩

#print axioms five_small_pattern_unique_split
end LC004

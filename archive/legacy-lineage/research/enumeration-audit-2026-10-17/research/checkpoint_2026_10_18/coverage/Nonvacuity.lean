import LC004.AllWitnessCancellation

namespace LC004

-- A twelve-position instance with four nonempty cyclic gaps. The top
-- remainder partition connects gap 0 (position 1) to gap 1 (position 4).
example : ¬(⊤ : Setoid (QuadRemainder (0 : Fin 12) 3 6 9)) ≤
    Setoid.ker (remainderGapIndex (0 : Fin 12) 3 6 9) := by
  intro h
  let x : QuadRemainder (0 : Fin 12) 3 6 9 := ⟨1,by decide⟩
  let y : QuadRemainder (0 : Fin 12) 3 6 9 := ⟨4,by decide⟩
  have he := @h x y (show (⊤ : Setoid _) x y from trivial)
  exact Nat.zero_ne_one (congrArg Fin.val he)

example : collectedCoeff (unionTerms (· ⊔ ·) (allPairTripleWitnesses 12))
    (fullBoardPartition (quadSplitEquiv (0 : Fin 12) 3 6 9 (by decide) (by decide) (by decide))
      ((⊤ : Setoid (Fin 4)),⊤)) = 0 := by
  apply all_witness_four_block_zero
  intro h
  let x : QuadRemainder (0 : Fin 12) 3 6 9 := ⟨1,by decide⟩
  let y : QuadRemainder (0 : Fin 12) 3 6 9 := ⟨4,by decide⟩
  have he := @h x y (show (⊤ : Setoid _) x y from trivial)
  exact Nat.zero_ne_one (congrArg Fin.val he)

end LC004

import LC004.GrammarErase
import LC004.RunLengthTwoThree

namespace LC004

/-- Removing an entire monochromatic run of length at least two can be
    represented by a finite sequence of adjacent pair/triple erasures,
    regardless of the surrounding left and right contexts. -/
theorem erase_full_monochromatic_run {q : Nat}
    (a : Fin q) (n : Nat) (hn : 2 ≤ n)
    (left right : List (Fin q)) :
    Erases (left ++ List.replicate n a ++ right) (left ++ right) := by
  induction n using Nat.strong_induction_on generalizing left right with
  | h n ih =>
      by_cases htwo : n = 2
      · subst n
        simpa [List.replicate, List.append_assoc] using
          (Erases.next (SmallErase.pair left right a)
            (Erases.refl (left ++ right)))
      by_cases hthree : n = 3
      · subst n
        simpa [List.replicate, List.append_assoc] using
          (Erases.next (SmallErase.triple left right a)
            (Erases.refl (left ++ right)))
      have hfour : 4 ≤ n := by omega
      have hlt : n - 2 < n := by omega
      have hprev : 2 ≤ n - 2 := by omega
      have hlen : n = 2 + (n - 2) := by omega
      have hrep : List.replicate n a =
          [a, a] ++ List.replicate (n - 2) a := by
        conv_lhs => rw [hlen]
        simp [List.replicate_add, List.replicate]
      have hstep :
          SmallErase (left ++ List.replicate n a ++ right)
            (left ++ List.replicate (n - 2) a ++ right) := by
        rw [hrep]
        simpa only [List.append_assoc] using
          (SmallErase.pair left (List.replicate (n - 2) a ++ right) a)
      exact Erases.next hstep (ih (n - 2) hlt hprev left right)

end LC004

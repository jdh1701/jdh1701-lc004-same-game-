import LC004.NoMergeExchangeInterior
import LC004.ListSplit
import LC004.ExchangeDominance
import LC004.ExecutableCorrespondence

namespace LC004

/-- The local relation needed after a far-left move: inserting a heavy run
between two contexts either makes the result heavier immediately (when the
boundary merges) or leaves a legal deletion back to the child state. -/
theorem inserted_heavy_exchange
    {left right : RunState} {c : Nat} :
    ∃ v : RunState,
      v = left ++ (c,true) :: right ∧
      ExchangeDominates (left ++ right) v := by
  let v : RunState := left ++ (c,true) :: right
  by_cases hleft : left = []
  · subst left
    have hs : IndexedStep v 0 right := by
      apply stepAt_sound
      simp [v, stepAt]
    exact ⟨v, rfl,
      ExchangeDominates.oneStep hs (heavier_refl right)⟩
  · by_cases hright : right = []
    · subst right
      have hs : IndexedStep v left.length left := by
        simpa [v] using
          (IndexedStep.noMerge
            (pre := left) (post := []) (c := c)
            (by intro p q hp hq; simp at hq))
      exact ⟨v, rfl,
        ExchangeDominates.oneStep hs (by simpa using heavier_refl left)⟩
    · obtain ⟨front, ⟨a,ba⟩, hleftEq, hlast⟩ :=
        exists_split_last left hleft
      cases right with
      | nil => contradiction
      | cons z zs =>
          rcases z with ⟨b,bb⟩
          by_cases hab : a = b
          · subst b
            let w : RunState := front ++ (a,true) :: zs
            have hs : IndexedStep v (front.length + 1) w := by
              rw [hleftEq] at ⊢
              simpa [v, w, List.append_assoc] using
                (IndexedStep.merge
                  (pre := front) (post := zs)
                  (c := a) (d := c) (bp := ba) (bq := bb))
            have hh :
                Heavier
                  (left ++ (a,bb) :: zs)
                  w := by
              rw [hleftEq]
              simp only [List.append_assoc, List.singleton_append]
              apply heavier_append (heavier_refl front)
              simp [Heavier]
            exact ⟨v, rfl, ExchangeDominates.oneStep hs hh⟩
          · have hb :
                ∀ p q, left.getLast? = some p →
                  ((b,bb) :: zs).head? = some q → p.1 ≠ q.1 := by
              intro p q hp hq
              have hp' : p = (a,ba) := by
                rw [hlast] at hp
                exact (Option.some.inj hp).symm
              have hq' : q = (b,bb) := by
                have hq0 : (b,bb) = q := by simpa using hq
                exact hq0.symm
              subst p
              subst q
              exact hab
            have hs :
                IndexedStep v left.length
                  (left ++ (b,bb) :: zs) := by
              simpa [v] using
                (IndexedStep.noMerge
                  (pre := left) (post := (b,bb) :: zs)
                  (c := c) hb)
            exact ⟨v, rfl,
              ExchangeDominates.oneStep hs
                (by simpa using heavier_refl (left ++ (b,bb) :: zs))⟩

end LC004

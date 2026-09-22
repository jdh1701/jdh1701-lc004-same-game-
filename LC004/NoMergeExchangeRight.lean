import LC004.ExchangeDominance
import LC004.ListSplit
import LC004.HeavierLemmas
import LC004.ExchangeScaffold
import LC004.IndexedMoveBounds

namespace LC004

/-- Right-edge critical pair. Appending a removable heavy run commutes with
any child move, except when deleting the child's last run exposes an equal
color on its left; then the alternate successor is a heavier child result. -/
theorem noMerge_exchange_right
    {pre u : RunState} {c : Nat} {j : Nat}
    (hchild : IndexedStep pre j u) :
    ∃ v : RunState,
      IndexedStep (pre ++ [(c,true)]) j v ∧
      ExchangeDominates u v := by
  cases hchild with
  | @noMerge left post d hboundary =>
      by_cases hpost : post = []
      · subst post
        simp only [List.append_nil]
        by_cases hleft : left = []
        · subst left
          let v : RunState := [(c,true)]
          have hp :
              IndexedStep
                ([(d,true)] ++ [(c,true)]) 0 v := by
            simpa [v] using
              (IndexedStep.noMerge
                (pre := []) (post := [(c,true)]) (c := d)
                (by intro p q hp hq; simp at hp))
          have hdel : IndexedStep v 0 ([] : RunState) := by
            simpa [v] using
              (IndexedStep.noMerge
                (pre := []) (post := []) (c := c)
                (by intro p q hp hq; simp at hp))
          exact ⟨v, hp,
            ExchangeDominates.oneStep hdel (heavier_refl [])⟩
        · obtain ⟨front, ⟨a,ba⟩, hleftEq, hlast⟩ :=
            exists_split_last left hleft
          by_cases hac : a = c
          · subst a
            let v : RunState := front ++ [(c,true)]
            have hp0 :
                IndexedStep
                  (front ++ (c,ba) :: (d,true) :: (c,true) :: [])
                  (front.length + 1) v := by
              simpa [v] using
                (IndexedStep.merge
                  (pre := front) (post := [])
                  (c := c) (d := d) (bp := ba) (bq := true))
            have hp :
                IndexedStep
                  ((left ++ [(d,true)]) ++ [(c,true)])
                  left.length v := by
              rw [hleftEq]
              simpa [List.append_assoc] using hp0
            have hlastHeavy :
                Heavier [(c,ba)] [(c,true)] := by
              simp [Heavier]
            have hh : Heavier left v := by
              rw [hleftEq]
              simpa [v] using
                heavier_append (heavier_refl front) hlastHeavy
            exact ⟨v, hp, ExchangeDominates.heavier hh⟩
          · let v : RunState := left ++ [(c,true)]
            have hb :
                ∀ p q, left.getLast? = some p →
                  [(c,true)].head? = some q → p.1 ≠ q.1 := by
              intro p q hp hq
              have hp' : p = (a,ba) := by
                rw [hlast] at hp
                exact Option.some.inj hp
              have hq' : q = (c,true) := by
                simpa using hq
              subst p
              subst q
              exact hac
            have hp :
                IndexedStep
                  ((left ++ [(d,true)]) ++ [(c,true)])
                  left.length v := by
              simpa [v, List.append_assoc] using
                (IndexedStep.noMerge
                  (pre := left) (post := [(c,true)]) (c := d) hb)
            have hdel :
                IndexedStep v left.length left := by
              simpa [v] using
                (IndexedStep.noMerge
                  (pre := left) (post := []) (c := c)
                  (by intro p q hp hq; simp at hq))
            exact ⟨v, hp,
              ExchangeDominates.oneStep hdel (heavier_refl left)⟩
      · cases post with
        | nil => contradiction
        | cons z zs =>
            let post' : RunState := (z :: zs) ++ [(c,true)]
            have hb :
                ∀ p q, left.getLast? = some p →
                  post'.head? = some q → p.1 ≠ q.1 := by
              intro p q hp hq
              apply hboundary p q hp
              simpa [post'] using hq
            let v : RunState :=
              (left ++ (z :: zs)) ++ [(c,true)]
            have hp :
                IndexedStep
                  ((left ++ (d,true) :: (z :: zs)) ++ [(c,true)])
                  left.length v := by
              simpa [v, post', List.append_assoc] using
                (IndexedStep.noMerge
                  (pre := left) (post := post') (c := d) hb)
            have hdel :
                IndexedStep v (left ++ (z :: zs)).length
                  (left ++ (z :: zs)) := by
              simpa [v] using
                (IndexedStep.noMerge
                  (pre := left ++ (z :: zs)) (post := []) (c := c)
                  (by intro p q hp hq; simp at hq))
            exact ⟨v, hp,
              ExchangeDominates.oneStep hdel
                (heavier_refl (left ++ (z :: zs)))⟩
  | @merge left post d e bp bq =>
      let v : RunState :=
        (left ++ (d,true) :: post) ++ [(c,true)]
      have hp :
          IndexedStep
            ((left ++ (d,bp) :: (e,true) :: (d,bq) :: post) ++
              [(c,true)])
            (left.length + 1) v := by
        simpa [v, List.append_assoc] using
          (IndexedStep.merge
            (pre := left) (post := post ++ [(c,true)])
            (c := d) (d := e) (bp := bp) (bq := bq))
      have hdel :
          IndexedStep v (left ++ (d,true) :: post).length
            (left ++ (d,true) :: post) := by
        simpa [v] using
          (IndexedStep.noMerge
            (pre := left ++ (d,true) :: post)
            (post := []) (c := c)
            (by intro p q hp hq; simp at hq))
      exact ⟨v, hp,
        ExchangeDominates.oneStep hdel
          (heavier_refl (left ++ (d,true) :: post))⟩

/-- The right-edge critical pair lifts every successful child choice to a
distinct successful parent choice. The index stays fixed, while the chosen
right-edge deletion sits at index `pre.length`. -/
theorem childChoicesLift_noMerge_right
    {pre : RunState} {c : Nat} :
    ChildChoicesLift
      (pre ++ [(c,true)])
      (pre.length, pre) := by
  intro childChoice hchild
  rcases childChoice with ⟨j,u⟩
  obtain ⟨v, hparent, hdom⟩ :=
    noMerge_exchange_right (c := c) hchild.1
  refine ⟨(j,v), ?_, ?_⟩
  · exact successfulChoice_of_exchangeDominates
      hparent hdom hchild.2
  · intro heq
    have hidx : j = pre.length :=
      congrArg Prod.fst heq
    have hjlt : j < pre.length :=
      indexedStep_index_lt hchild.1
    omega


end LC004

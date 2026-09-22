import LC004.RunState
import LC004.HeavierLemmas
import LC004.SplitRunLemmas
import LC004.BoundaryLemmas
import LC004.Transition

namespace LC004

/-- Interior no-merge simulation in an explicit boundary decomposition.
Deleting the heavy middle run exposes colors a and b with a != b; Heavier
preserves those colors and hence preserves the no-merge condition. -/
theorem deleteSimulation_noMerge_interior
    {left right : RunState}
    {a b c : Nat} {ba bb : Bool} {t : RunState}
    (hab : a ≠ b)
    (h :
      Heavier
        (left ++ (a,ba) :: (c,true) :: (b,bb) :: right)
        t) :
    ∃ v : RunState,
      Step t v ∧
      Heavier
        (left ++ (a,ba) :: (b,bb) :: right)
        v := by
  obtain ⟨pre1, tail1, ea, ht1, hea, hleft, hrest⟩ :=
    heavier_split_run left ((c,true)::(b,bb)::right) a ba h
  obtain ⟨pre2, tail2, ec, ht2, hec, hmid, hrest2⟩ :=
    heavier_split_run [] ((b,bb)::right) c true hrest
  have hpre2 : pre2 = [] := by
    cases pre2 <;> simp_all [Heavier]
  subst pre2
  have hectrue : ec = true := by
    cases ec <;> simp_all
  subst ec
  obtain ⟨eb, right', htail, heb, hright⟩ :=
    heavier_head_shape hrest2
  subst tail2
  subst tail1
  rw [ht1]
  refine ⟨pre1 ++ (a,ea)::(b,eb)::right', ?_, ?_⟩
  · exact Step.noMerge (by
      intro p q hp hq
      have hp' : p = (a,ea) := by
        simpa using hp
      have hq' : q = (b,eb) := by
        simpa using hq
      subst p
      subst q
      simpa using hab)
  · apply heavier_append hleft
    simp only [Heavier]
    exact ⟨trivial, hea, trivial, heb, hright⟩

end LC004

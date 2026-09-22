import LC004.IndexedMove
import LC004.RunState

namespace LC004

def headColor? (s : RunState) : Option Nat :=
  s.head?.map Prod.fst

theorem indexedStep_nonzero_headColor
    {s t : RunState} {i : Nat}
    (hi : i ≠ 0)
    (h : IndexedStep s i t) :
    headColor? s = headColor? t := by
  cases h with
  | @noMerge pre post c hboundary =>
      have hpre : pre ≠ [] := by
        intro hp
        subst pre
        simp at hi
      cases pre with
      | nil => contradiction
      | cons x xs =>
          simp [headColor?]
  | @merge pre post c d bp bq =>
      cases pre with
      | nil =>
          simp [headColor?]
      | cons x xs =>
          simp [headColor?]

theorem heavier_headColor
    {s t : RunState}
    (h : Heavier s t) :
    headColor? s = headColor? t := by
  cases s with
  | nil =>
      cases t <;> simp [Heavier, headColor?] at h ⊢
  | cons x xs =>
      cases t with
      | nil =>
          simp [Heavier] at h
      | cons y ys =>
          rcases x with ⟨c,b⟩
          rcases y with ⟨d,e⟩
          simp [Heavier] at h
          simp [headColor?, h.1]


/-- Transfer a no-merge boundary inequality across states with the same head
color.  The Bool payload is irrelevant; only the exposed run color matters. -/
theorem boundary_of_headColor_eq
    {pre s t : RunState}
    (heq : headColor? s = headColor? t)
    (hb : ∀ p q,
      pre.getLast? = some p →
      s.head? = some q →
      p.1 ≠ q.1) :
    ∀ p q,
      pre.getLast? = some p →
      t.head? = some q →
      p.1 ≠ q.1 := by
  intro p q hp hq
  cases t with
  | nil =>
      simp at hq
  | cons tq ts =>
      rcases tq with ⟨tc,tb⟩
      have hq' : q = (tc,tb) := by
        simpa using hq.symm
      subst q
      cases s with
      | nil =>
          simp [headColor?] at heq
      | cons sq ss =>
          rcases sq with ⟨sc,sb⟩
          have hsc : sc = tc := by
            simpa [headColor?] using heq
          have hneq := hb p (sc,sb) hp (by simp)
          simpa [hsc] using hneq

end LC004

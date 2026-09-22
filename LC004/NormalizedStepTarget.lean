import LC004.RunState
import LC004.Normalized
import LC004.NormalizedAppend
import LC004.Transition

namespace LC004

theorem normalized_step
    {s t : RunState}
    (hn : Normalized s)
    (hs : Step s t) :
    Normalized t := by
  cases hs with
  | @noMerge pre post c hboundary =>
      rw [normalized_append_iff] at ⊢
      have hsrc :
          Normalized pre ∧
          Normalized ((c,true)::post) ∧
          (∀ p q, pre.getLast? = some p →
            ((c,true)::post).head? = some q → p.1 ≠ q.1) := by
        exact (normalized_append_iff pre ((c,true)::post)).mp hn
      have htail : Normalized post := normalized_tail hsrc.2.1
      exact ⟨hsrc.1, htail, hboundary⟩
  | @merge pre post c d bp bq =>
      have hsrc1 :=
        (normalized_append_iff pre ((c,bp)::(d,true)::(c,bq)::post)).mp hn
      have hright : Normalized ((c,bq)::post) := by
        exact normalized_tail (normalized_tail hsrc1.2.1)
      have hpost : Normalized post := normalized_tail hright
      have hleftBoundary :
          ∀ p q, pre.getLast? = some p →
            ((c,true)::post).head? = some q → p.1 ≠ q.1 := by
        intro p q hp hq
        have hqeq : q = (c,true) := by simpa using hq
        subst q
        exact hsrc1.2.2 p (c,bp) hp (by rfl)
      exact (normalized_append_iff pre ((c,true)::post)).mpr
        ⟨hsrc1.1, by
          cases post with
          | nil => simp [Normalized]
          | cons z zs =>
              rcases z with ⟨e,be⟩
              have hcb : c ≠ e := by
                have hsuffix : Normalized ((c,bq)::(e,be)::zs) := hright
                simpa [Normalized] using hsuffix.1
              simpa [Normalized] using And.intro hcb hpost,
          hleftBoundary⟩

end LC004

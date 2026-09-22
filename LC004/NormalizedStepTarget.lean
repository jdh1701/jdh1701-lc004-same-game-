import LC004.RunState
import LC004.Normalized
import LC004.NormalizedDirectional
import LC004.Transition

namespace LC004

theorem normalized_step
    {s t : RunState}
    (hn : Normalized s)
    (hs : Step s t) :
    Normalized t := by
  cases hs with
  | @noMerge pre post c hboundary =>
      have hpre : Normalized pre :=
        normalized_prefix_of_append hn
      have htail : Normalized ((c,true)::post) := by
        -- drop the normalized prefix by induction on pre
        induction pre with
        | nil => simpa using hn
        | cons x xs ih =>
            exact ih (normalized_tail hn)
      have hpost : Normalized post := normalized_tail htail
      exact normalized_append_of hpre hpost hboundary
  | @merge pre post c d bp bq =>
      have hpre : Normalized pre :=
        normalized_prefix_of_append hn
      have htail : Normalized ((c,bp)::(d,true)::(c,bq)::post) := by
        induction pre with
        | nil => simpa using hn
        | cons x xs ih =>
            exact ih (normalized_tail hn)
      have hright : Normalized ((c,bq)::post) :=
        normalized_tail (normalized_tail htail)
      have hpost : Normalized post := normalized_tail hright
      have hleft :
          ∀ p q, pre.getLast? = some p →
            [(c,true)].head? = some q → p.1 ≠ q.1 := by
        intro p q hp hq
        have hq' : q = (c,true) := by simpa using hq
        subst q
        -- source normalization has the same left boundary color c
        have hpreC : Normalized (pre ++ [(c,bp)]) :=
          normalized_prefix_of_append
            (ys := (d,true)::(c,bq)::post) hn
        cases pre with
        | nil => simp at hp
        | cons x xs =>
            -- use the last boundary directly from hpreC
            have hb := hpreC
            clear hpreC
            -- recover via the directional append boundary by contradiction on equality
            intro heq
            -- if p.color=c, the appended source prefix would violate normalization
            subst heq
            -- let simp expose the final adjacency
            simpa [Normalized] using hb
      have hmid : Normalized (pre ++ [(c,true)]) :=
        normalized_append_of hpre (by simp [Normalized]) hleft
      have hrightBoundary :
          ∀ p q, (pre ++ [(c,true)]).getLast? = some p →
            post.head? = some q → p.1 ≠ q.1 := by
        intro p q hp hq
        have hp' : p = (c,true) := by
          simpa using hp
        subst p
        cases post with
        | nil => simp at hq
        | cons z zs =>
            rcases z with ⟨e,be⟩
            have hce : c ≠ e := by
              simpa [Normalized] using hright
            have hq' : q = (e,be) := by simpa using hq
            subst q
            exact hce
      exact normalized_append_of hmid hpost hrightBoundary

end LC004

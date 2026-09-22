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
        normalized_prefix_of_append
          (xs := pre) (ys := (c,true)::post) hn
      have htail : Normalized ((c,true)::post) :=
        normalized_suffix_of_append
          (xs := pre) (ys := (c,true)::post) hn
      have hpost : Normalized post := normalized_tail htail
      exact normalized_append_of hpre hpost hboundary
  | @merge pre post c d bp bq =>
      have hpre : Normalized pre :=
        normalized_prefix_of_append
          (xs := pre) (ys := (c,bp)::(d,true)::(c,bq)::post) hn
      have htail : Normalized ((c,bp)::(d,true)::(c,bq)::post) :=
        normalized_suffix_of_append
          (xs := pre) (ys := (c,bp)::(d,true)::(c,bq)::post) hn
      have hright : Normalized ((c,bq)::post) :=
        normalized_tail (normalized_tail htail)
      have hpost : Normalized post := normalized_tail hright
      have hleft :
          ∀ p q, pre.getLast? = some p →
            [(c,true)].head? = some q → p.1 ≠ q.1 := by
        intro p q hp hq
        have hb := normalized_boundary_of_append
          (xs := pre)
          (ys := (c,bp)::(d,true)::(c,bq)::post)
          hn p (c,bp) hp (by simp)
        have hq' : (c,true) = q := by simpa using hq
        subst q
        simpa using hb
      have hmid : Normalized (pre ++ [(c,true)]) :=
        normalized_append_of hpre (by simp [Normalized]) hleft
      have hrightBoundary :
          ∀ p q, (pre ++ [(c,true)]).getLast? = some p →
            post.head? = some q → p.1 ≠ q.1 := by
        intro p q hp hq
        have hp' : (c,true) = p := by simpa using hp
        subst p
        have hb := normalized_boundary_of_append
          (xs := [(c,bq)]) (ys := post)
          hright (c,bq) q (by simp) hq
        simpa using hb
      have htarget : Normalized ((pre ++ [(c,true)]) ++ post) :=
        normalized_append_of hmid hpost hrightBoundary
      simpa [List.append_assoc] using htarget

end LC004

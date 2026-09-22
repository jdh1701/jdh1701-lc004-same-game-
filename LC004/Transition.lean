import LC004.RunState

namespace LC004

/-- A move deletes one selected heavy run. The successor is represented by
    list prefix/suffix decomposition; when deletion exposes equal-colored
    boundary runs, those two runs are replaced by one heavy run. -/
inductive Step : RunState → RunState → Prop
  | noMerge {pre post : RunState} {c : Nat}
      (hboundary : ∀ p q,
        pre.getLast? = some p → post.head? = some q → p.1 ≠ q.1) :
      Step (pre ++ (c,true) :: post) (pre ++ post)
  | merge {pre post : RunState} {c d : Nat} {bp bq : Bool} :
      Step (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
           (pre ++ (c,true) :: post)

end LC004

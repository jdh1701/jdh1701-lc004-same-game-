import LC004.ExecutableCorrespondence
import LC004.SuccessfulPaths

namespace LC004

/-- A selected run index has at most one relational successor. -/
theorem indexedStep_target_unique
    {s t u : RunState} {i : Nat}
    (ht : IndexedStep s i t)
    (hu : IndexedStep s i u) :
    t = u := by
  have hte := stepAt_complete ht
  have hue := stepAt_complete hu
  have : some t = some u := hte.symm.trans hue
  exact Option.some.inj this

/-- Successful indexed choices with the same selected run index are equal. -/
theorem successfulChoice_eq_of_index_eq
    {s : RunState} {a b : Nat × RunState}
    (ha : SuccessfulChoice s a)
    (hb : SuccessfulChoice s b)
    (hi : a.1 = b.1) :
    a = b := by
  rcases a with ⟨ia, ta⟩
  rcases b with ⟨ib, tb⟩
  simp only at hi
  subst ib
  have ht : ta = tb := indexedStep_target_unique ha.1 hb.1
  subst tb
  rfl

end LC004

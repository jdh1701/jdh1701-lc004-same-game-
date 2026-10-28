import LC004.FullRunErasure

namespace LC004

/-- A legal raw Same Game step deletes an *entire maximal run*
of at least two equal-colored cells. The boundary inequalities are
what distinguish maximal-run moves from arbitrary block erasure. -/
inductive RawMaxStep {q : Nat} :
    List (Fin q) → List (Fin q) → Prop where
  | delete (left right : List (Fin q)) (a : Fin q)
      (n : Nat) (hn : 2 ≤ n)
      (hleft : left.getLast? ≠ some a)
      (hright : right.head? ≠ some a) :
      RawMaxStep
        (left ++ List.replicate n a ++ right)
        (left ++ right)

/-- Zero or more genuine maximal-run moves. -/
inductive RawMaxErases {q : Nat} :
    List (Fin q) → List (Fin q) → Prop where
  | refl (w : List (Fin q)) : RawMaxErases w w
  | next {u v w : List (Fin q)} :
      RawMaxStep u v → RawMaxErases v w → RawMaxErases u w

/-- Each legal original-game move refines to a finite sequence of
auxiliary pair/triple erasures. -/
theorem raw_max_step_to_erases {q : Nat}
    {u v : List (Fin q)} (h : RawMaxStep u v) :
    Erases u v := by
  cases h with
  | delete left right a n hn hleft hright =>
      exact erase_full_monochromatic_run a n hn left right

/-- One unconditional direction of the semantics bridge:
every complete maximal-run deletion path admits an auxiliary
pair/triple erasure path with the same endpoints. -/
theorem raw_max_path_to_erases {q : Nat}
    {u v : List (Fin q)} (h : RawMaxErases u v) :
    Erases u v := by
  induction h with
  | refl w => exact Erases.refl w
  | next hstep hrest ih =>
      exact erases_trans (raw_max_step_to_erases hstep) ih

/-- In particular, every ordinary raw Same Game winning position is
erasable by the pair/triple auxiliary relation. -/
theorem raw_max_win_to_aux_erases {q : Nat}
    {w : List (Fin q)} (h : RawMaxErases w []) :
    Erases w [] := raw_max_path_to_erases h

end LC004

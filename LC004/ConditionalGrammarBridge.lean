import LC004.GrammarErase

namespace LC004

/-- An abstract target winning predicate is backward-closed under auxiliary
    pair/triple deletions. This explicit hypothesis is the open mathematical
    bridge to maximal-run Same Game; it is NOT asserted as an axiom. -/
theorem erases_imply_win_of_one_step_lift {q : Nat}
    (Win : List (Fin q) → Prop)
    (emptyWin : Win [])
    (lift : ∀ {u v : List (Fin q)}, SmallErase u v → Win v → Win u)
    {w : List (Fin q)} (h : Erases w []) : Win w := by
  have aux : ∀ {u v : List (Fin q)}, Erases u v → Win v → Win u := by
    intro u v huv
    induction huv with
    | refl _ =>
        intro hv
        exact hv
    | next step rest ih =>
        intro hv
        exact lift step (ih hv)
  exact aux h emptyWin

/-- Conditional grammar soundness. To use this for the original maximal-run
    game one MUST separately prove its one-step lifting property. -/
theorem grammar_implies_win_of_one_step_lift {q : Nat}
    (Win : List (Fin q) → Prop)
    (emptyWin : Win [])
    (lift : ∀ {u v : List (Fin q)}, SmallErase u v → Win v → Win u)
    {w : List (Fin q)} (h : Grammar q w) : Win w := by
  exact erases_imply_win_of_one_step_lift Win emptyWin lift
    (grammar_erases_empty h)

end LC004

import LC004.RawMaxSemanticsBridge

namespace LC004

/-- A sequence of legal maximal-run deletions composes. -/
theorem raw_max_erases_trans {q : Nat}
    {u v w : List (Fin q)}
    (huv : RawMaxErases u v)
    (hvw : RawMaxErases v w) :
    RawMaxErases u w := by
  induction huv with
  | refl _ => exact hvw
  | next step rest ih =>
      exact RawMaxErases.next step (ih hvw)

/-- Insertion of an isolated monochromatic block is a genuine
maximal-run move in reverse. The boundary colors of the *outer*
word may be equal to one another; only their difference from a
matters. -/
theorem isolated_block_raw_step {q : Nat}
    (left right : List (Fin q)) (a : Fin q)
    (n : Nat) (hn : 2 ≤ n)
    (hleft : left.getLast? ≠ some a)
    (hright : right.head? ≠ some a) :
    RawMaxStep (left ++ List.replicate n a ++ right)
      (left ++ right) := by
  exact RawMaxStep.delete left right a n hn hleft hright

/-- Unconditional raw-game insertion closure for a block not touching
any existing run of its color. Includes insertion in the middle of
an existing run of a DIFFERENT color. -/
theorem isolated_block_preserves_raw_win {q : Nat}
    (left right : List (Fin q)) (a : Fin q)
    (n : Nat) (hn : 2 ≤ n)
    (hleft : left.getLast? ≠ some a)
    (hright : right.head? ≠ some a)
    (hw : RawMaxErases (left ++ right) []) :
    RawMaxErases (left ++ List.replicate n a ++ right) [] := by
  exact RawMaxErases.next
    (isolated_block_raw_step left right a n hn hleft hright) hw

end LC004

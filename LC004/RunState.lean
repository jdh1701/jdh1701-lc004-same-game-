import Mathlib

namespace LC004

abbrev RunState := List (Nat × Bool)

def Heavier : RunState → RunState → Prop
  | [], [] => True
  | (c,b)::xs, (d,e)::ys => c = d ∧ (b → e) ∧ Heavier xs ys
  | _, _ => False

theorem heavier_refl : ∀ s : RunState, Heavier s s := by
  intro s
  induction s with
  | nil => trivial
  | cons x xs ih =>
      rcases x with ⟨c,b⟩
      simp [Heavier, ih]

def upgradeAt : Nat → RunState → RunState
  | _, [] => []
  | 0, (c,_)::xs => (c,true)::xs
  | n+1, x::xs => x :: upgradeAt n xs

theorem heavier_upgradeAt (s : RunState) (i : Nat) :
    Heavier s (upgradeAt i s) := by
  induction s generalizing i with
  | nil => simp [upgradeAt, Heavier]
  | cons x xs ih =>
      rcases x with ⟨c,b⟩
      cases i with
      | zero => simp [upgradeAt, Heavier, heavier_refl]
      | succ i => simp [upgradeAt, Heavier, ih]

end LC004

import LC004.ExchangeTarget
import LC004.ExecutableCorrespondence

namespace LC004

def forceHeadHeavy : RunState → RunState
  | [] => []
  | (c, _) :: xs => (c, true) :: xs

theorem stepAt_forceHead_succ
    (s : RunState) (i : Nat) :
    stepAt (forceHeadHeavy s) (i + 1) =
      (stepAt s (i + 1)).map forceHeadHeavy := by
  cases s with
  | nil =>
      simp [forceHeadHeavy, stepAt]
  | cons x xs =>
      rcases x with ⟨c,b⟩
      cases xs with
      | nil =>
          simp [forceHeadHeavy, stepAt]
      | cons y post =>
          rcases y with ⟨d,e⟩
          cases i with
          | zero =>
              cases e with
              | false =>
                  simp [forceHeadHeavy, stepAt]
              | true =>
                  cases post with
                  | nil =>
                      simp [forceHeadHeavy, stepAt]
                  | cons z zs =>
                      rcases z with ⟨f,g⟩
                      by_cases hcf : c = f
                      · simp [forceHeadHeavy, stepAt, hcf]
                      · simp [forceHeadHeavy, stepAt, hcf]
          | succ j =>
              cases htail : stepAt ((d,e) :: post) (j + 1) with
              | none =>
                  simp [forceHeadHeavy, stepAt, htail]
              | some t =>
                  simp [forceHeadHeavy, stepAt, htail]

theorem stepAt_succ_preserves_head_color
    {c : Nat} {b : Bool} {post u : RunState} {i : Nat}
    (h : stepAt ((c,b) :: post) (i + 1) = some u) :
    ∃ e rest, u = (c,e) :: rest := by
  cases post with
  | nil =>
      simp [stepAt] at h
  | cons y tail =>
      rcases y with ⟨d,e⟩
      cases i with
      | zero =>
          cases e with
          | false =>
              simp [stepAt] at h
          | true =>
              cases tail with
              | nil =>
                  simp [stepAt] at h
                  subst u
                  exact ⟨b, [], rfl⟩
              | cons z zs =>
                  rcases z with ⟨f,g⟩
                  by_cases hcf : c = f
                  · simp [stepAt, hcf] at h
                    subst f
                    subst u
                    exact ⟨true, zs, rfl⟩
                  · simp [stepAt, hcf] at h
                    subst u
                    exact ⟨b, (f,g) :: zs, rfl⟩
      | succ j =>
          cases htail : stepAt ((d,e) :: tail) (j + 1) with
          | none =>
              simp [stepAt, htail] at h
          | some t =>
              simp [stepAt, htail] at h
              subst u
              exact ⟨b, t, rfl⟩

/-- Base right-side bridge diamond.  The parent bridge has empty prefix.
A successful child move strictly to the right of the newly merged run lifts
two indices to the right in the parent; after that lifted move, deleting the
original bridge reaches the child successor exactly. -/
theorem bridge_front_right_exchange
    {post u : RunState} {c d : Nat} {bp bq : Bool} {i : Nat}
    (hchild : IndexedStep ((c,true) :: post) (i + 1) u) :
    ∃ v : RunState,
      IndexedStep
        ((c,bp) :: (d,true) :: (c,bq) :: post)
        (i + 3) v ∧
      ExchangeTarget u v := by
  have hchildExec :
      stepAt ((c,true) :: post) (i + 1) = some u :=
    stepAt_complete hchild
  have hforce :=
    stepAt_forceHead_succ ((c,bq) :: post) i
  have hforce' :
      stepAt ((c,true) :: post) (i + 1) =
        (stepAt ((c,bq) :: post) (i + 1)).map forceHeadHeavy := by
    simpa [forceHeadHeavy] using hforce
  rw [hchildExec] at hforce'
  cases hraw : stepAt ((c,bq) :: post) (i + 1) with
  | none =>
      simp [hraw] at hforce'
  | some u0 =>
      have hfu : forceHeadHeavy u0 = u := by
        simpa [hraw] using hforce'.symm
      obtain ⟨e, rest, hu0⟩ :=
        stepAt_succ_preserves_head_color hraw
      subst u0
      have hu : u = (c,true) :: rest := by
        simpa [forceHeadHeavy] using hfu.symm
      let v : RunState := (c,bp) :: (d,true) :: (c,e) :: rest
      have hparentExec :
          stepAt
            ((c,bp) :: (d,true) :: (c,bq) :: post)
            (i + 3) = some v := by
        simp [stepAt, hraw, v, Nat.add_assoc]
      have hparent :
          IndexedStep
            ((c,bp) :: (d,true) :: (c,bq) :: post)
            (i + 3) v :=
        stepAt_sound hparentExec
      have hsecond :
          IndexedStep v 1 ((c,true) :: rest) := by
        simpa [v] using
          (IndexedStep.merge
            (pre := []) (post := rest)
            (c := c) (d := d) (bp := bp) (bq := e))
      subst u
      exact ⟨v, hparent, ExchangeTarget.oneStep hsecond⟩

end LC004

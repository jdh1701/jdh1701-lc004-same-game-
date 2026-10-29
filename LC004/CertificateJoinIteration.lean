import LC004.CertificateConstraintJoins

namespace LC004
open scoped Classical

/-- Signed join terms, retaining duplicates so that no normalization is needed. -/
noncomputable def certificateJoinTerms {n : Nat} :
    List (ColorPattern n) → List (ColorPattern n × Int)
  | [] => []
  | c :: cs => (c, 1) :: (certificateJoinTerms cs ++
      (certificateJoinTerms cs).map (fun t => (t.1 ⊔ c, -t.2)))

noncomputable def joinTermScore {n : Nat}
    (ts : List (ColorPattern n × Int)) (r : ColorPattern n) : Int :=
  (ts.map (fun t => t.2 * constraintIndicator t.1 r)).sum

theorem joinTermScore_intersections {n : Nat}
    (ts : List (ColorPattern n × Int)) (c r : ColorPattern n) :
    joinTermScore (ts.map (fun t => (t.1 ⊔ c, -t.2))) r =
      -(joinTermScore ts r * constraintIndicator c r) := by
  induction ts with
  | nil => simp [joinTermScore]
  | cons t ts ih =>
    simp only [List.map_cons, joinTermScore, List.sum_cons] at ih ⊢
    rw [ih, constraintIndicator_join]
    ring

/-- The entire signed expansion is the indicator of admitting at least one
constraint. Duplicated constraints and the empty list are both allowed. -/
theorem certificateJoinTerms_score {n : Nat} (cs : List (ColorPattern n))
    (r : ColorPattern n) :
    joinTermScore (certificateJoinTerms cs) r =
      if ∃ c ∈ cs, c ≤ r then 1 else 0 := by
  classical
  induction cs with
  | nil => simp [certificateJoinTerms, joinTermScore]
  | cons c cs ih =>
    have hstep : joinTermScore (certificateJoinTerms (c :: cs)) r =
        constraintIndicator c r + joinTermScore (certificateJoinTerms cs) r -
          joinTermScore (certificateJoinTerms cs) r * constraintIndicator c r := by
      simp only [certificateJoinTerms, joinTermScore, List.map_cons,
        List.map_append, List.sum_cons, List.sum_append, one_mul]
      change _ + (_ + joinTermScore
        ((certificateJoinTerms cs).map (fun t => (t.1 ⊔ c, -t.2))) r) = _
      rw [joinTermScore_intersections]
      ring
    rw [hstep, ih]
    by_cases hc : c ≤ r <;> by_cases hs : ∃ d ∈ cs, d ≤ r <;>
      simp [constraintIndicator, hc, hs]

/-- Any exact finite generating family immediately gives the game's indicator. -/
theorem certificateJoinTerms_winning_indicator {n : Nat}
    (cs : List (ColorPattern n))
    (hcs : ∀ r, WinningColorPattern r ↔ ∃ c ∈ cs, c ≤ r)
    (r : ColorPattern n) :
    joinTermScore (certificateJoinTerms cs) r =
      if WinningColorPattern r then 1 else 0 := by
  classical
  rw [certificateJoinTerms_score, ← hcs r]

#print axioms certificateJoinTerms_score
#print axioms certificateJoinTerms_winning_indicator
end LC004

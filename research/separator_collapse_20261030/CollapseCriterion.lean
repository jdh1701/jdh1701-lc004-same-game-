import LC004.IncidenceFaceSum
import Lean.Util.CollectAxioms

namespace LC004.SeparatorCollapse
open scoped BigOperators

/-- An actual elementary free-face collapse, excluding the empty face. -/
def Elementary {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) : Prop :=
  ∃ s t, s ∈ F ∧ t ∈ F ∧ s.Nonempty ∧ t.card = s.card + 1 ∧
    (∀ u ∈ F, s ⊆ u → u = s ∨ u = t) ∧ G = (F.erase s).erase t

theorem erase_pair_preserves {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (s t : Finset α)
    (hs : s ∈ F) (ht : t ∈ F) (hcard : t.card = s.card + 1) :
    faceAlternatingSum ((F.erase s).erase t) = faceAlternatingSum F := by
  classical
  have hne : t ≠ s := by intro h; subst t; omega
  have ht' : t ∈ F.erase s := Finset.mem_erase.mpr ⟨hne, ht⟩
  have h1 := Finset.sum_erase_add F (fun u : Finset α => (-1 : Int)^u.card) hs
  have h2 := Finset.sum_erase_add (F.erase s)
    (fun u : Finset α => (-1 : Int)^u.card) ht'
  have hc : (-1 : Int)^t.card + (-1 : Int)^s.card = 0 := by
    rw [hcard, pow_succ]
    ring
  unfold faceAlternatingSum
  linarith

theorem elementary_preserves {α : Type*} [DecidableEq α]
    {F G : Finset (Finset α)} (h : Elementary F G) :
    faceAlternatingSum F = faceAlternatingSum G := by
  obtain ⟨s,t,hs,ht,_,hc,_,rfl⟩ := h
  exact (erase_pair_preserves F s t hs ht hc).symm

theorem path_preserves {α : Type*} [DecidableEq α]
    {F G : Finset (Finset α)} (h : Relation.ReflTransGen Elementary F G) :
    faceAlternatingSum F = faceAlternatingSum G := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (elementary_preserves hstep)

theorem point_sum {α : Type*} [DecidableEq α] (v : α) :
    faceAlternatingSum ({∅, {v}} : Finset (Finset α)) = 0 := by
  classical
  unfold faceAlternatingSum
  rw [Finset.sum_pair (by simp : (∅ : Finset α) ≠ {v})]
  simp

/-- A collapse of the actual indexed separator complex certifies zero for
its ORIGINAL Same Game coefficient, without restrictions on class sizes. -/
theorem original_coefficient_zero {n : Nat} {β : Type*} [DecidableEq β]
    (p : ColorPattern n) (V : Finset β) (sep : β → ColorPattern n)
    (hproper : ∀ v ∈ V, sep v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ sep v)
    (v : β)
    (hcollapse : Relation.ReflTransGen Elementary
      (facetFaces (indexedCertificateCoarseningFacets p V sep)) {∅, {v}}) :
    winningJoinCoefficient n p = 0 := by
  rw [winningJoinCoefficient_eq_indexed_face_sum p V sep hproper hcover]
  rw [path_preserves hcollapse]
  exact point_sum v

open Lean Elab Command in
run_cmd do
  for name in [``erase_pair_preserves, ``elementary_preserves, ``path_preserves,
      ``point_sum, ``original_coefficient_zero] do
    let axs ← collectAxioms name
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Forbidden axiom {ax} in {name}"
  logInfo "SEPARATOR COLLAPSE AUDIT PASS: five theorems"
end LC004.SeparatorCollapse

import LC004.ChoiceFunctionalElimination

namespace LC004

def choiceCoordinateLift {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (b : ∀ k, E k) : ∀ i, D i :=
  fun i => e i (b (r i))

noncomputable def choiceReducedFamily {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) : Finset (∀ k, E k) := by
  classical
  exact Finset.univ.filter (fun b => choiceCoordinateLift r e b ∈ A)

theorem mem_choiceReducedFamily {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (b : ∀ k, E k) :
    b ∈ choiceReducedFamily A r e ↔ choiceCoordinateLift r e b ∈ A := by
  classical
  simp [choiceReducedFamily]

theorem choiceCoordinateLift_injective {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (hr : Function.Surjective r) :
    Function.Injective (choiceCoordinateLift r e) := by
  intro b c h
  funext k
  obtain ⟨i, rfl⟩ := hr k
  exact (e i).injective (congrFun h i)

theorem choiceMajority_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y z : α) :
    e (choiceMajority x y z) = choiceMajority (e x) (e y) (e z) := by
  by_cases h : y = z
  · simp [choiceMajority, h]
  · have h' : e y ≠ e z := fun hh => h (e.injective hh)
    simp [choiceMajority, h, h']

theorem choiceReducedFamily_closed {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)]
    [∀ i, DecidableEq (D i)] [∀ k, DecidableEq (E k)]
    (A : Finset (∀ i, D i)) (r : ι → κ) (e : ∀ i, E (r i) ≃ D i)
    (hclosed : ChoiceSolutionsClosed A) :
    ChoiceSolutionsClosed (choiceReducedFamily A r e) := by
  intro a ha b hb c hc
  apply (mem_choiceReducedFamily A r e _).mpr
  have h := hclosed _ ((mem_choiceReducedFamily A r e a).mp ha)
    _ ((mem_choiceReducedFamily A r e b).mp hb)
    _ ((mem_choiceReducedFamily A r e c).mp hc)
  have heq : choiceCoordinateLift r e (fun k => choiceMajority (a k) (b k) (c k)) =
      (fun i => choiceMajority (choiceCoordinateLift r e a i)
        (choiceCoordinateLift r e b i) (choiceCoordinateLift r e c i)) := by
    funext i
    exact choiceMajority_equiv (e i) _ _ _
  rw [heq]
  exact h

theorem choiceReducedFamily_support {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (hr : Function.Surjective r)
    (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hcover : ∀ a ∈ A, ∃ b, choiceCoordinateLift r e b = a) :
    ∀ k x, ∃ b ∈ choiceReducedFamily A r e, b k = x := by
  intro k x
  obtain ⟨i, rfl⟩ := hr k
  obtain ⟨a, ha, hai⟩ := hsupport i (e i x)
  obtain ⟨b, hb⟩ := hcover a ha
  refine ⟨b, (mem_choiceReducedFamily A r e b).mpr (hb.symm ▸ ha), ?_⟩
  apply (e i).injective
  change choiceCoordinateLift r e b i = e i x
  rw [hb]
  exact hai

theorem choiceReducedFamily_pair {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i)
    (hcover : ∀ a ∈ A, ∃ b, choiceCoordinateLift r e b = a)
    (i j : ι) (x : E (r i)) (y : E (r j)) :
    ChoicePairProjection (choiceReducedFamily A r e) (r i) (r j) x y ↔
      ChoicePairProjection A i j (e i x) (e j y) := by
  constructor
  · rintro ⟨b, hb, hbi, hbj⟩
    exact ⟨_, (mem_choiceReducedFamily A r e b).mp hb,
      congrArg (e i) hbi, congrArg (e j) hbj⟩
  · rintro ⟨a, ha, hai, haj⟩
    obtain ⟨b, hb⟩ := hcover a ha
    refine ⟨b, (mem_choiceReducedFamily A r e b).mpr (hb.symm ▸ ha), ?_, ?_⟩
    · apply (e i).injective
      change choiceCoordinateLift r e b i = _
      rw [hb]
      exact hai
    · apply (e j).injective
      change choiceCoordinateLift r e b j = _
      rw [hb]
      exact haj

/-- Projection onto coherent bijective representatives preserves the binary
description, including pairs of old coordinates sharing one representative. -/
theorem choiceReducedFamily_binary {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (hr : Function.Surjective r)
    (hsupport : ∀ i x, ∃ a ∈ A, a i = x)
    (hcover : ∀ a ∈ A, ∃ b, choiceCoordinateLift r e b = a)
    (hbinary : ChoiceBinaryDetermined A) :
    ChoiceBinaryDetermined (choiceReducedFamily A r e) := by
  intro b hlocal
  apply (mem_choiceReducedFamily A r e b).mpr
  apply hbinary
  intro i j hij
  apply (choiceReducedFamily_pair A r e hcover i j _ _).mp
  by_cases h : r i = r j
  · obtain ⟨c, hc, hci⟩ := choiceReducedFamily_support A r e hr hsupport hcover (r i) (b (r i))
    refine ⟨c, hc, hci, ?_⟩
    exact Eq.mp (congrArg (fun k => c k = b k) h) hci
  · exact hlocal (r i) (r j) h

/-- Connectedness stated by crossing every proper nonempty cut, so it can be
transported through a surjection without an injective graph-map assumption. -/
def ChoiceCoordinatesConnected {ι : Type*} {D : ι → Type*}
    (A : Finset (∀ i, D i)) : Prop :=
  ∀ S : Set ι, S.Nonempty → Sᶜ.Nonempty →
    ∃ i ∈ S, ∃ j ∉ S, ¬ ∀ x y, ChoicePairProjection A i j x y

theorem choiceReducedFamily_connected {ι κ : Type*} {D : ι → Type*} {E : κ → Type*}
    [Fintype κ] [∀ k, Fintype (E k)] (A : Finset (∀ i, D i))
    (r : ι → κ) (e : ∀ i, E (r i) ≃ D i) (hr : Function.Surjective r)
    (hcover : ∀ a ∈ A, ∃ b, choiceCoordinateLift r e b = a)
    (hconn : ChoiceCoordinatesConnected A) :
    ChoiceCoordinatesConnected (choiceReducedFamily A r e) := by
  intro S hS hSc
  obtain ⟨k, hk⟩ := hS
  obtain ⟨l, hl⟩ := hSc
  obtain ⟨i, rfl⟩ := hr k
  obtain ⟨j, rfl⟩ := hr l
  obtain ⟨u, hu, v, hv, hn⟩ := hconn (r ⁻¹' S) ⟨i, hk⟩ ⟨j, hl⟩
  refine ⟨r u, hu, r v, hv, ?_⟩
  intro hall
  apply hn
  intro x y
  have h := (choiceReducedFamily_pair A r e hcover u v
    ((e u).symm x) ((e v).symm y)).mp (hall _ _)
  simpa using h

theorem choiceCoordinatesConnected_neighbors {ι : Type*} {D : ι → Type*}
    [Nontrivial ι] (A : Finset (∀ i, D i)) (hconn : ChoiceCoordinatesConnected A) :
    ∀ i, ∃ j, i ≠ j ∧ ¬ ∀ x y, ChoicePairProjection A i j x y := by
  intro i
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨u, hu, v, hv, hn⟩ := hconn {i} ⟨i, rfl⟩ ⟨j, hj⟩
  have hui : u = i := hu
  subst u
  exact ⟨v, fun h => hv h.symm, hn⟩

#print axioms choiceReducedFamily_binary
#print axioms choiceReducedFamily_connected
#print axioms choiceReducedFamily_closed
end LC004

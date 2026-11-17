import LC004.PartitionCounting
import LC004.CoefficientTransport

namespace LC004

/-- Put two equivalence relations on disjoint parts of a carrier. -/
def separatedPartition {α β : Type*} (p : Setoid α × Setoid β) : Setoid (α ⊕ β) where
  r := Sum.LiftRel p.1.r p.2.r
  iseqv := {
    refl := by
      intro x
      cases x with
      | inl a => exact Sum.LiftRel.inl (p.1.refl a)
      | inr b => exact Sum.LiftRel.inr (p.2.refl b)
    symm := by
      intro x y h
      cases h with
      | inl h => exact Sum.LiftRel.inl (p.1.symm h)
      | inr h => exact Sum.LiftRel.inr (p.2.symm h)
    trans := by
      intro x y z hxy hyz
      cases hxy with
      | inl hxy =>
        cases hyz with
        | inl hyz => exact Sum.LiftRel.inl (p.1.trans hxy hyz)
      | inr hxy =>
        cases hyz with
        | inr hyz => exact Sum.LiftRel.inr (p.2.trans hxy hyz) }

theorem separatedPartition_le_iff {α β : Type*}
    (p : Setoid α × Setoid β) (t : Setoid (α ⊕ β)) :
    separatedPartition p ≤ t ↔
      p.1 ≤ Setoid.comap Sum.inl t ∧ p.2 ≤ Setoid.comap Sum.inr t := by
  constructor
  · intro h
    exact ⟨fun {_ _} hxy => h (Sum.LiftRel.inl hxy),fun {_ _} hxy => h (Sum.LiftRel.inr hxy)⟩
  · rintro ⟨hl,hr⟩ x y h
    cases h with
    | inl h => exact hl h
    | inr h => exact hr h

theorem separatedPartition_restrictions {α β : Type*} (p : Setoid α × Setoid β) :
    (Setoid.comap Sum.inl (separatedPartition p),
      Setoid.comap Sum.inr (separatedPartition p)) = p := by
  apply Prod.ext
  · exact Setoid.ext (fun _ _ => Sum.liftRel_inl_inl)
  · exact Setoid.ext (fun _ _ => Sum.liftRel_inr_inr)

theorem separatedPartition_le_separated_iff {α β : Type*}
    (p q : Setoid α × Setoid β) : separatedPartition p ≤ separatedPartition q ↔ p ≤ q := by
  rw [separatedPartition_le_iff]
  have h := separatedPartition_restrictions q
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change Setoid.comap Sum.inl (separatedPartition q) = q.1 at hl
  change Setoid.comap Sum.inr (separatedPartition q) = q.2 at hr
  change p.1 ≤ (Setoid.comap Sum.inl (separatedPartition q)) ∧
    p.2 ≤ (Setoid.comap Sum.inr (separatedPartition q)) ↔ _
  rw [hl,hr]
  rfl

theorem separatedPartition_injective {α β : Type*} :
    Function.Injective (separatedPartition (α := α) (β := β)) := by
  intro p q h
  have he := congrArg (fun t => (Setoid.comap Sum.inl t,Setoid.comap Sum.inr t)) h
  simpa only [separatedPartition_restrictions] using he

/-- The ambient join is the join in ALL equivalence relations. It respects
the separated product, so no noncrossing-join substitution is involved. -/
theorem separatedPartition_sup {α β : Type*} (p q : Setoid α × Setoid β) :
    separatedPartition (p ⊔ q) = separatedPartition p ⊔ separatedPartition q := by
  apply le_antisymm
  · apply (separatedPartition_le_iff _ _).mpr
    constructor
    · apply sup_le
      · intro a b h
        exact (le_sup_left : separatedPartition p ≤ separatedPartition p ⊔ separatedPartition q)
          (Sum.LiftRel.inl h)
      · intro a b h
        exact (le_sup_right : separatedPartition q ≤ separatedPartition p ⊔ separatedPartition q)
          (Sum.LiftRel.inl h)
    · apply sup_le
      · intro a b h
        exact (le_sup_left : separatedPartition p ≤ separatedPartition p ⊔ separatedPartition q)
          (Sum.LiftRel.inr h)
      · intro a b h
        exact (le_sup_right : separatedPartition q ≤ separatedPartition p ⊔ separatedPartition q)
          (Sum.LiftRel.inr h)
  · exact sup_le
      ((separatedPartition_le_separated_iff _ _).mpr le_sup_left)
      ((separatedPartition_le_separated_iff _ _).mpr le_sup_right)

theorem separatedPartition_reconstruct {α β : Type*} (t : Setoid (α ⊕ β))
    (ht : t ≤ separatedPartition ((⊤ : Setoid α),(⊤ : Setoid β))) :
    separatedPartition (Setoid.comap Sum.inl t,Setoid.comap Sum.inr t) = t := by
  apply Setoid.ext
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b => exact Sum.liftRel_inl_inl
    | inr b =>
      constructor
      · intro h; cases h
      · intro h; cases ht h
  | inr a =>
    cases y with
    | inl b =>
      constructor
      · intro h; cases h
      · intro h; cases ht h
    | inr b => exact Sum.liftRel_inr_inr

/-- Explicit product order isomorphism for partitions that keep two parts
separate. Restriction and reconstruction are inverse maps. -/
def separatedPartitionOrderIso (α β : Type*) :
    (Setoid α × Setoid β) ≃o
      {t : Setoid (α ⊕ β) // t ≤ separatedPartition ((⊤ : Setoid α),(⊤ : Setoid β))} where
  toFun p := ⟨separatedPartition p,(separatedPartition_le_separated_iff _ _).mpr le_top⟩
  invFun t := (Setoid.comap Sum.inl t.val,Setoid.comap Sum.inr t.val)
  left_inv := separatedPartition_restrictions
  right_inv t := Subtype.ext (separatedPartition_reconstruct t.val t.property)
  map_rel_iff' := separatedPartition_le_separated_iff _ _

/-- Relabel a partition along a bijection of carriers. -/
def relabelPartitions {α β : Type*} (e : α ≃ β) : Setoid β ≃o Setoid α where
  toFun := Setoid.comap e
  invFun := Setoid.comap e.symm
  left_inv r := Setoid.ext (fun x y => by simp only [Setoid.comap_rel,e.apply_symm_apply])
  right_inv r := Setoid.ext (fun x y => by simp only [Setoid.comap_rel,e.symm_apply_apply])
  map_rel_iff' := by
    intro r s
    constructor
    · intro h x y hxy
      have hs : Setoid.comap e s (e.symm x) (e.symm y) :=
        h (by simpa only [Setoid.comap_rel,e.apply_symm_apply] using hxy)
      simpa only [Setoid.comap_rel,e.apply_symm_apply] using hs
    · intro h x y hxy
      exact h hxy

/-- Embed product coordinates as an actual partition of the whole carrier. -/
def fullBoardPartition {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (p : Setoid α × Setoid β) : Setoid γ :=
  relabelPartitions e (separatedPartition p)

theorem fullBoardPartition_injective {α β γ : Type*} (e : γ ≃ α ⊕ β) :
    Function.Injective (fullBoardPartition e) :=
  (relabelPartitions e).injective.comp separatedPartition_injective

theorem fullBoardPartition_sup {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (p q : Setoid α × Setoid β) :
    fullBoardPartition e (p ⊔ q) = fullBoardPartition e p ⊔ fullBoardPartition e q := by
  unfold fullBoardPartition
  rw [separatedPartition_sup,OrderIso.map_sup]

theorem fullBoard_coefficient_transport {α β γ : Type*} (e : γ ≃ α ⊕ β)
    (ps : List (Setoid α × Setoid β)) (p : Setoid α × Setoid β) :
    collectedCoeff (unionTerms (· ⊔ ·) (ps.map (fullBoardPartition e))) (fullBoardPartition e p) =
      collectedCoeff (unionTerms (· ⊔ ·) ps) p :=
  collected_union_transport _ (fullBoardPartition_injective e) (fullBoardPartition_sup e) ps p

end LC004

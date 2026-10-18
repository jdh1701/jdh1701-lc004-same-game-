import LC004.CoefficientLocality

namespace LC004

/-- Transport every signed key along a join-preserving map. -/
theorem unionTerms_map_sup {P Q : Type*} [SemilatticeSup P] [SemilatticeSup Q]
    (f : P → Q) (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (ps : List P) :
    unionTerms (· ⊔ ·) (ps.map f) =
      (unionTerms (· ⊔ ·) ps).map (fun t => (t.1,f t.2)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [unionTerms, addConstraint, ih, List.map_map, Function.comp_def, hf]

/-- An injective key map preserves the coefficient at the image of each key. -/
theorem collectedCoeff_map_injective {P Q : Type*}
    (f : P → Q) (hf : Function.Injective f) (ts : SignedTerms P) (p : P) :
    collectedCoeff (ts.map (fun t => (t.1,f t.2))) (f p) = collectedCoeff ts p := by
  classical
  simp [collectedCoeff, List.map_map, Function.comp_def, hf.eq_iff]

/-- Coefficient transport through an injective join-preserving map. This works
without enumerating the ambient partition lattice. -/
theorem collected_union_transport {P Q : Type*} [SemilatticeSup P] [SemilatticeSup Q]
    (f : P → Q) (hinj : Function.Injective f)
    (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (ps : List P) (p : P) :
    collectedCoeff (unionTerms (· ⊔ ·) (ps.map f)) (f p) =
      collectedCoeff (unionTerms (· ⊔ ·) ps) p := by
  rw [unionTerms_map_sup f hsup, collectedCoeff_map_injective f hinj]

end LC004

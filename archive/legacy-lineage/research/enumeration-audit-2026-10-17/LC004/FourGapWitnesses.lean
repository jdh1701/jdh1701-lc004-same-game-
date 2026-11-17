import LC004.WitnessGluing
import LC004.FourBlockCancellation

namespace LC004

def adjacentGapLabel (i : Fin 4) : Nat :=
  if i = 0 then 0 else if i = 2 then 2 else 1

def nestedGapLabel (i : Fin 4) : Nat :=
  if i = 1 then 1 else if i = 3 then 3 else 0

/-- Keep gaps 0 and 2 separate, allowing gaps 1 and 3 to share blocks. -/
def adjacentGapRegions {α : Type*} (gap : α → Fin 4) : Setoid α :=
  Setoid.ker (adjacentGapLabel ∘ gap)

/-- Keep gaps 1 and 3 separate, allowing gaps 0 and 2 to share blocks. -/
def nestedGapRegions {α : Type*} (gap : α → Fin 4) : Setoid α :=
  Setoid.ker (nestedGapLabel ∘ gap)

/-- The two actual regional witness conditions intersect in four separate
gap witnesses. This theorem constructs the witness; it does not assume the
intersection-invariance condition used by the coefficient theorem. -/
theorem four_gap_witness_intersection {α : Type*} [LinearOrder α] [Finite α]
    (gap : α → Fin 4) (hg : IsNoncrossing (Setoid.ker gap)) (p : Setoid α) :
    (WitnessUnder (adjacentGapRegions gap) p ∧
      WitnessUnder (nestedGapRegions gap) p) ↔ WitnessUnder (Setoid.ker gap) p := by
  let U := fun x => gap x = 0 ∨ gap x = 2
  apply witness_intersection_glue _ _ _ U hg
  · intro x y h
    exact congrArg adjacentGapLabel h
  · intro x y h
    exact congrArg nestedGapLabel h
  · intro x y h
    have hl : ∀ i j : Fin 4, adjacentGapLabel i = adjacentGapLabel j →
        ((i = 0 ∨ i = 2) ↔ (j = 0 ∨ j = 2)) := by decide
    exact hl (gap x) (gap y) h
  · intro x y h
    have hl : ∀ i j : Fin 4, nestedGapLabel i = nestedGapLabel j →
        ((i = 0 ∨ i = 2) ↔ (j = 0 ∨ j = 2)) := by decide
    exact hl (gap x) (gap y) h
  · intro x y hx h
    have hl : ∀ i j : Fin 4, (i = 0 ∨ i = 2) →
        adjacentGapLabel i = adjacentGapLabel j → i = j := by decide
    exact hl (gap x) (gap y) hx h
  · intro x y hx h
    have hl : ∀ i j : Fin 4, ¬(i = 0 ∨ i = 2) →
        nestedGapLabel i = nestedGapLabel j → i = j := by decide
    exact hl (gap x) (gap y) hx h

theorem witnessUnder_meet {α : Type*} [LinearOrder α] [Finite α]
    (g p : Setoid α) : WitnessUnder g p ↔ WitnessUnder g (p ⊓ g) := by
  constructor
  · rintro ⟨r,hr,hrg,hrp⟩
    exact ⟨r,hr,hrg,le_inf hrp hrg⟩
  · rintro ⟨r,hr,hrg,hrp⟩
    exact ⟨r,hr,hrg,le_trans hrp inf_le_left⟩

/-- Any finite list enumerating a regional witness family has its intended
existential coverage, independently of list order and duplicates. -/
theorem witness_list_coverage {α : Type*} [LinearOrder α] [Finite α]
    (A : Setoid α) (ps : List (Setoid α))
    (hps : ∀ r, r ∈ ps ↔ PairTriplePartition r ∧ r ≤ A) (p : Setoid α) :
    (∃ r ∈ ps, r ≤ p) ↔ WitnessUnder A p := by
  constructor
  · rintro ⟨r,hm,hrp⟩
    exact ⟨r,((hps r).mp hm).1,((hps r).mp hm).2,hrp⟩
  · rintro ⟨r,hr,hrA,hrp⟩
    exact ⟨r,(hps r).mpr ⟨hr,hrA⟩,hrp⟩

/-- The former `hinv` obligation is discharged for lists of the two regional
pair/triple witness families. Only their enumeration specifications remain
as list hypotheses. -/
theorem four_gap_join_coverage_invariant {α : Type*} [LinearOrder α] [Finite α]
    (gap : α → Fin 4) (hg : IsNoncrossing (Setoid.ker gap))
    (ps qs : List (Setoid α))
    (hps : ∀ r, r ∈ ps ↔ PairTriplePartition r ∧ r ≤ adjacentGapRegions gap)
    (hqs : ∀ r, r ∈ qs ↔ PairTriplePartition r ∧ r ≤ nestedGapRegions gap)
    (p : Setoid α) :
    (∃ r ∈ joinWitnessLists ps qs, r ≤ p) ↔
      (∃ r ∈ joinWitnessLists ps qs, r ≤ p ⊓ Setoid.ker gap) := by
  simp only [joinWitnessLists_covered,
    witness_list_coverage _ ps hps, witness_list_coverage _ qs hqs,
    four_gap_witness_intersection gap hg]
  exact witnessUnder_meet _ _

/-- Cancellation outside the four-gap barrier for the specified regional
witness families, with geometric invariance proved above rather than assumed. -/
theorem four_gap_witness_coefficient_zero {α : Type*} [LinearOrder α] [Finite α]
    (gap : α → Fin 4) (hg : IsNoncrossing (Setoid.ker gap))
    (ps qs : List (Setoid α))
    (hps : ∀ r, r ∈ ps ↔ PairTriplePartition r ∧ r ≤ adjacentGapRegions gap)
    (hqs : ∀ r, r ∈ qs ↔ PairTriplePartition r ∧ r ≤ nestedGapRegions gap)
    (p : Setoid α) (hp : ¬p ≤ Setoid.ker gap) :
    collectedCoeff (unionTerms (· ⊔ ·)
      ((ps.map fun r => (quadAdjacent,r)) ++ (qs.map fun r => (quadNested,r))))
      ((⊤ : Setoid (Fin 4)),p) = 0 := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Finite (Setoid α) := Finite.of_injective (fun s : Setoid α => s.r)
    (fun s t h => Setoid.ext (fun a b => iff_of_eq (congrFun (congrFun h a) b)))
  letI : Fintype (Setoid α) := Fintype.ofFinite _
  exact four_block_barrier_zero ps qs (Setoid.ker gap) p
    (four_gap_join_coverage_invariant gap hg ps qs hps hqs) hp

end LC004

import LC004.FourGapGeometry

namespace LC004

/-- A finite specification of all partitions on a finite carrier. This is
noncomputable and makes no claim about the executable generator. -/
noncomputable def partitionFintype (α : Type*) [Finite α] : Fintype (Setoid α) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Finite (Setoid α) := Finite.of_injective (fun s : Setoid α => s.r)
    (fun s t h => Setoid.ext (fun a b => iff_of_eq (congrFun (congrFun h a) b)))
  exact Fintype.ofFinite _

/-- The complete finite family of pair/triple witnesses under a barrier.
This is a specification list, not an efficient enumeration algorithm. -/
noncomputable def regionalWitnessList {α : Type*} [LinearOrder α] [Finite α]
    (A : Setoid α) : List (Setoid α) := by
  classical
  letI := partitionFintype α
  exact (Finset.univ.filter (fun r => PairTriplePartition r ∧ r ≤ A)).toList

theorem mem_regionalWitnessList {α : Type*} [LinearOrder α] [Finite α]
    (A r : Setoid α) :
    r ∈ regionalWitnessList A ↔ PairTriplePartition r ∧ r ≤ A := by
  classical
  simp [regionalWitnessList]

/-- The four-position product-coordinate branch family. Relating this family
to all witnesses refining a full board partition is a separate obligation. -/
noncomputable def regionalFourBlockFamily {α : Type*} [LinearOrder α] [Finite α]
    (gap : α → Fin 4) : List (Setoid (Fin 4) × Setoid α) :=
  ((regionalWitnessList (adjacentGapRegions gap)).map fun r => (quadAdjacent,r)) ++
  ((regionalWitnessList (nestedGapRegions gap)).map fun r => (quadNested,r))

/-- Cancellation for the complete specified regional families: there is no
assumed witness-list completeness or intersection-invariance premise. -/
theorem regional_four_block_zero {α : Type*} [LinearOrder α] [Finite α]
    (gap : α → Fin 4) (hg : IsNoncrossing (Setoid.ker gap))
    (p : Setoid α) (hp : ¬p ≤ Setoid.ker gap) :
    collectedCoeff (unionTerms (· ⊔ ·) (regionalFourBlockFamily gap))
      ((⊤ : Setoid (Fin 4)),p) = 0 := by
  exact four_gap_witness_coefficient_zero gap hg _ _
    (mem_regionalWitnessList _) (mem_regionalWitnessList _) p hp

/-- For any four ordered board positions, the complete regional branch family
has zero coefficient at a remainder partition connecting distinct cyclic gaps.
The coefficient is still expressed in product coordinates. -/
theorem positional_regional_four_block_zero {n : Nat} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (p : Setoid (QuadRemainder a b c d))
    (hp : ¬p ≤ Setoid.ker (remainderGapIndex a b c d)) :
    collectedCoeff (unionTerms (· ⊔ ·)
      (regionalFourBlockFamily (remainderGapIndex a b c d)))
      ((⊤ : Setoid (Fin 4)),p) = 0 := by
  exact regional_four_block_zero _ (remainderGapIndex_noncrossing a b c d hab hbc hcd) p hp

end LC004

import LC004.FiveClassGeometryExhaustive

namespace LC004

/-- Every pair of increasing ranks occurs among the ten choices. -/
theorem fivePairRanks_complete : ∀ u v : Fin 5, u < v →
    ∃ s : Fin 10, fivePairRanks s = [u.val, v.val] := by
  decide +kernel

theorem fivePairRanks_valid : ∀ s : Fin 10, ∃ u v : Fin 5,
    u < v ∧ fivePairRanks s = [u.val, v.val] := by
  decide +kernel

theorem fivePairRanks_injective : Function.Injective fivePairRanks := by
  unfold Function.Injective
  decide +kernel

/-- The four split blocks placed by an increasing map of the rank line. -/
def FivePlacedCompatible (f : Nat → Nat) (g h : List Nat) (x y : Fin 10) : Prop :=
  NoncrossingBlockFamily
    ((fiveSplitBlocks g x ++ fiveSplitBlocks h y).map (List.map f))

theorem fivePlacedCompatible_iff (f : Nat → Nat) (hf : StrictMono f)
    (g h : List Nat) (x y : Fin 10) :
    FivePlacedCompatible f g h x y ↔ FiveCompatible g h x y := by
  exact (noncrossingBlockFamily_map_strictMono_iff f hf _).trans
    (fiveCompatible_iff g h x y).symm

/-- The finite computation supplies both local cancellation inputs at arbitrary
increasing placements of the ten ranks. No gap sizes occur in the conclusion. -/
theorem fiveClass_placed_geometry (f : Nat → Nat) (hf : StrictMono f)
    (g : List Nat) (hg : g ∈ (List.range 10).sublistsLen 5) :
    ChoiceRelationClosed (FivePlacedCompatible f g (fiveOtherRanks g)) ∧
      (BlocksCross (g.map f) ((fiveOtherRanks g).map f) →
        ∃ p q : Fin 10, ∀ x y,
          FivePlacedCompatible f g (fiveOtherRanks g) x y → x = p ∨ y = q) := by
  obtain ⟨hclosed, hcover⟩ := fiveClass_finite_geometry g hg
  refine ⟨(choiceRelationClosed_congr (fivePlacedCompatible_iff f hf g _)).mpr hclosed, ?_⟩
  intro hcross
  obtain ⟨p, q, hpq⟩ := hcover ((blocksCross_map_strictMono_iff f hf g _).mp hcross)
  exact ⟨p, q, fun x y hxy => hpq x y ((fivePlacedCompatible_iff f hf g _ x y).mp hxy)⟩

#print axioms fiveClass_placed_geometry
end LC004

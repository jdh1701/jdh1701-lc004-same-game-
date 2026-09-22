import LC004.FinalAssembly
import LC004.NoMergeStructuralProof
import LC004.BridgeStructuralFinal

namespace LC004

/-- Unconditional normalized run-state theorem: uniqueness of the successful
first deletion is equivalent to uniqueness of the complete successful path. -/
theorem unconditional_unique_choice_iff_unique_path
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulChoice s ↔ UniqueCompletePath s := by
  exact final_unique_choice_iff_unique_path
    noMergeStructuralExchange_proved
    normalizedBridgeStructuralExchange_proved
    hn hne

/-- Executable-index formulation of the unconditional theorem. -/
theorem unconditional_executable_unique_first_iff_path
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulFirst s ↔ UniqueSuccessfulPath s := by
  exact final_executable_unique_first_iff_path
    noMergeStructuralExchange_proved
    normalizedBridgeStructuralExchange_proved
    hn hne

#print axioms unconditional_unique_choice_iff_unique_path
#print axioms unconditional_executable_unique_first_iff_path

end LC004

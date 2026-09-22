import LC004.ExecutableUniqueness
import LC004.ConditionalMain
import LC004.NoMergeExchangeAssembly
import LC004.BridgeExchangeAssembly

namespace LC004

/-- Final assembly theorem.  Once the two concrete structural exchange laws
are proved, the target equivalence follows with no additional Same-Game
mathematics. -/
theorem final_unique_choice_iff_unique_path
    (hnoStruct : NoMergeStructuralExchange)
    (hbridgeStruct : NormalizedBridgeStructuralExchange)
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulChoice s ↔ UniqueCompletePath s := by
  exact uniqueSuccessfulChoice_iff_uniqueCompletePath_exchange
    (normalizedNoMergeExchange_of_structural hnoStruct)
    (normalizedBridgeExchange_of_structural hbridgeStruct)
    hn hne

/-- Executable formulation of the same final target. -/
theorem final_executable_unique_first_iff_path
    (hnoStruct : NoMergeStructuralExchange)
    (hbridgeStruct : NormalizedBridgeStructuralExchange)
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulFirst s ↔ UniqueSuccessfulPath s := by
  rw [uniqueSuccessfulFirst_iff_uniqueSuccessfulChoice,
      uniqueSuccessfulPath_iff_uniqueCompletePath]
  exact final_unique_choice_iff_unique_path
    hnoStruct hbridgeStruct hn hne

end LC004

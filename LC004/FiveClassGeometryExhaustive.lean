import LC004.FiveClassGeometryCases0
import LC004.FiveClassGeometryCases1
import LC004.FiveClassGeometryCases2
import LC004.FiveClassGeometryCases3
import LC004.FiveClassGeometryCases4
import LC004.FiveClassGeometryCases5

namespace LC004

def fiveInterleavingInventory : List (List Nat) :=
  fiveGeometryChunk0 ++ fiveGeometryChunk1 ++ fiveGeometryChunk2 ++ fiveGeometryChunk3 ++ fiveGeometryChunk4 ++ fiveGeometryChunk5

theorem fiveInterleavingInventory_count : fiveInterleavingInventory.length = 252 := by decide +kernel

/-- Every sorted five-element subset of the ten ranks appears in the checked inventory. -/
theorem fiveInterleavingInventory_complete :
    ((List.range 10).sublistsLen 5).all (fun g => fiveInterleavingInventory.contains g) = true := by
  decide +kernel

/-- Kernel-checked local geometry for every five-versus-five rank interleaving. -/
theorem fiveClass_finite_geometry (g : List Nat)
    (hg : g ∈ (List.range 10).sublistsLen 5) : FiveGeometryCase g := by
  have hm := (List.all_eq_true.mp fiveInterleavingInventory_complete) g hg
  have hi : g ∈ fiveInterleavingInventory := List.contains_iff_mem.mp hm
  simp only [fiveInterleavingInventory, List.mem_append, or_assoc] at hi
  rcases hi with h | h | h | h | h | h
  · exact fiveGeometryChunk0_checked g h
  · exact fiveGeometryChunk1_checked g h
  · exact fiveGeometryChunk2_checked g h
  · exact fiveGeometryChunk3_checked g h
  · exact fiveGeometryChunk4_checked g h
  · exact fiveGeometryChunk5_checked g h

#print axioms fiveClass_finite_geometry
end LC004

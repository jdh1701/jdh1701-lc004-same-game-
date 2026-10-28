import Mathlib

namespace LC004

/-- Every deletable run length is a sum of pair- and triple-length chunks.
This is the arithmetic core of refining maximal-run deletions into
auxiliary two/three-cell erasures. -/
theorem run_length_two_three (n : Nat) (hn : 2 ≤ n) :
    ∃ pairs triples : Nat, n = 2 * pairs + 3 * triples := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases htwo : n = 2
      · subst n
        exact ⟨1, 0, by omega⟩
      by_cases hthree : n = 3
      · subst n
        exact ⟨0, 1, by omega⟩
      have hfour : 4 ≤ n := by omega
      have hlt : n - 2 < n := by omega
      obtain ⟨pairs, triples, hrep⟩ :=
        ih (n - 2) hlt (by omega)
      exact ⟨pairs + 1, triples, by omega⟩

/-- In particular, a run of size at least two has an explicitly
representable pair/triple decomposition, with a nonzero number of chunks. -/
theorem run_length_two_three_nonempty (n : Nat) (hn : 2 ≤ n) :
    ∃ pairs triples : Nat,
      n = 2 * pairs + 3 * triples ∧ 0 < pairs + triples := by
  obtain ⟨pairs, triples, h⟩ := run_length_two_three n hn
  exact ⟨pairs, triples, h, by omega⟩

end LC004

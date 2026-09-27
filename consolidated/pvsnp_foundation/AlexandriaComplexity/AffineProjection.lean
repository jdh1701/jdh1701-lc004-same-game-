import Std

namespace AlexandriaComplexity.AffineProjection

abbrev Bits := List Bool

-- Truncating XOR and coordinate selection. For fixed-length vectors these are
-- ordinary XOR and coordinate projection. No integer encoding is assumed.
def xorV : Bits → Bits → Bits
  | a :: as, b :: bs => Bool.xor a b :: xorV as bs
  | _, _ => []

def select : List Bool → Bits → Bits
  | true :: ms, b :: bs => b :: select ms bs
  | false :: ms, _ :: bs => select ms bs
  | _, _ => []

theorem select_xor (mask : List Bool) (u v : Bits) :
    select mask (xorV u v) = xorV (select mask u) (select mask v) := by
  induction mask generalizing u v with
  | nil => rfl
  | cons bit mask ih =>
      cases u with
      | nil => cases bit <;> rfl
      | cons a as =>
          cases v with
          | nil =>
              cases bit with
              | false =>
                  change [] = xorV (select mask as) []
                  cases select mask as <;> rfl
              | true => rfl
          | cons b bs => cases bit <;> simp [select, xorV, ih]

-- Every generator is either omitted or XORed into the seed.
def Generated (seed : Bits) : List Bits → Bits → Prop
  | [], out => out = seed
  | g :: gs, out => Generated seed gs out ∨ Generated (xorV seed g) gs out

theorem generated_project (mask : List Bool) (gs : List Bits)
    (seed out : Bits) (h : Generated seed gs out) :
    Generated (select mask seed) (gs.map (select mask)) (select mask out) := by
  induction gs generalizing seed with
  | nil => exact congrArg (select mask) h
  | cons g gs ih =>
      cases h with
      | inl h => exact Or.inl (ih seed h)
      | inr h =>
          apply Or.inr
          have hp := ih (xorV seed g) h
          rw [select_xor] at hp
          exact hp

theorem generated_lift (mask : List Bool) (gs : List Bits)
    (seed projected : Bits)
    (h : Generated (select mask seed) (gs.map (select mask)) projected) :
    ∃ full, Generated seed gs full ∧ select mask full = projected := by
  induction gs generalizing seed with
  | nil => exact ⟨seed, rfl, h.symm⟩
  | cons g gs ih =>
      cases h with
      | inl h =>
          obtain ⟨full, hr, he⟩ := ih seed h
          exact ⟨full, Or.inl hr, he⟩
      | inr h =>
          have hp : Generated (select mask (xorV seed g))
              (gs.map (select mask)) projected := by
            rw [select_xor]
            exact h
          obtain ⟨full, hr, he⟩ := ih (xorV seed g) hp
          exact ⟨full, Or.inr hr, he⟩

theorem projected_search_complete (mask : List Bool) (gs : List Bits)
    (seed : Bits) (accept : Bits → Prop) :
    (∃ full, Generated seed gs full ∧ accept (select mask full)) ↔
    (∃ projected, Generated (select mask seed) (gs.map (select mask)) projected ∧
      accept projected) := by
  constructor
  · intro ⟨full, hr, ha⟩
    exact ⟨select mask full, generated_project mask gs seed full hr, ha⟩
  · intro ⟨projected, hr, ha⟩
    obtain ⟨full, hf, he⟩ := generated_lift mask gs seed projected hr
    exact ⟨full, hf, he.symm ▸ ha⟩

end AlexandriaComplexity.AffineProjection

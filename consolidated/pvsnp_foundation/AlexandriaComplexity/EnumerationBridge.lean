import AlexandriaComplexity.CoefficientChecker
import AlexandriaComplexity.AffineProjection

namespace AlexandriaComplexity.EnumerationBridge
open AffineProjection CoefficientChecker SpanReduction

def zeros : Nat → Bits
  | 0 => []
  | n + 1 => false :: zeros n

def runCoefficients (seed : Bits) (gs : List Bits) (cs : List Bool) : Option Bits :=
  match gs with
  | [] => match cs with
    | [] => some seed
    | _ :: _ => none
  | g :: tail => match cs with
    | [] => none
    | b :: rest => runCoefficients (if b then xorV seed g else seed) tail rest
termination_by structural gs

theorem zeros_length (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem xor_length (u v : Bits) (h : u.length = v.length) :
    (xorV u v).length = u.length := by
  induction u generalizing v with
  | nil => rfl
  | cons a us ih =>
      cases v with
      | nil => cases h
      | cons b vs => exact congrArg Nat.succ (ih vs (Nat.succ.inj h))

theorem xor_zero_right (u : Bits) : xorV u (zeros u.length) = u := by
  induction u with
  | nil => rfl
  | cons a us ih => cases a <;> exact congrArg (List.cons _) ih

theorem xor_zero_left (u : Bits) : xorV (zeros u.length) u = u := by
  induction u with
  | nil => rfl
  | cons a us ih => cases a <;> exact congrArg (List.cons _) ih

theorem xor_associative (u v w : Bits) :
    xorV (xorV u v) w = xorV u (xorV v w) := by
  induction u generalizing v w with
  | nil => rfl
  | cons a us ih =>
      cases v with
      | nil => rfl
      | cons b vs =>
          cases w with
          | nil => rfl
          | cons c ws =>
              cases a <;> cases b <;> cases c <;>
                exact congrArg (List.cons _) (ih vs ws)

theorem run_iff_generated (gs : List Bits) (seed out : Bits) :
    (∃ cs, runCoefficients seed gs cs = some out) ↔ Generated seed gs out := by
  induction gs generalizing seed with
  | nil =>
      constructor
      · intro ⟨cs, h⟩
        cases cs with
        | nil => exact (Option.some.inj h).symm
        | cons b bs => cases h
      · intro h
        exact ⟨[], congrArg some h.symm⟩
  | cons g gs ih =>
      constructor
      · intro ⟨cs, h⟩
        cases cs with
        | nil => cases h
        | cons b bs =>
            cases b with
            | false => exact Or.inl ((ih seed).mp ⟨bs, h⟩)
            | true => exact Or.inr ((ih (xorV seed g)).mp ⟨bs, h⟩)
      · intro h
        cases h with
        | inl h =>
            obtain ⟨cs, hc⟩ := (ih seed).mpr h
            exact ⟨false :: cs, hc⟩
        | inr h =>
            obtain ⟨cs, hc⟩ := (ih (xorV seed g)).mpr h
            exact ⟨true :: cs, hc⟩

theorem evaluate_width (n : Nat) (gs : List Bits)
    (width : ∀ g, g ∈ gs → g.length = n) (cs : List Bool) (out : Bits)
    (h : evaluate (zeros n) xorV gs cs = some out) : out.length = n := by
  induction gs generalizing cs out with
  | nil =>
      cases cs with
      | nil =>
          have e : zeros n = out := Option.some.inj h
          cases e
          exact zeros_length n
      | cons b bs => cases h
  | cons g gs ih =>
      have wg := width g (List.Mem.head gs)
      have wt : ∀ v, v ∈ gs → v.length = n := fun v hv => width v (List.Mem.tail g hv)
      cases cs with
      | nil => cases h
      | cons b bs =>
          change (match evaluate (zeros n) xorV gs bs with
            | none => none | some v => some (if b then xorV g v else v)) = some out at h
          cases ev : evaluate (zeros n) xorV gs bs with
          | none => rw [ev] at h; cases h
          | some v =>
              have wv := ih wt bs v ev
              rw [ev] at h
              cases b with
              | false =>
                  have e : v = out := Option.some.inj h
                  exact e ▸ wv
              | true =>
                  have e : xorV g v = out := Option.some.inj h
                  exact e ▸ (Eq.trans (xor_length g v (Eq.trans wg wv.symm)) wg)

theorem run_evaluate (n : Nat) (gs : List Bits)
    (width : ∀ g, g ∈ gs → g.length = n) (seed : Bits)
    (sw : seed.length = n) (cs : List Bool) :
    runCoefficients seed gs cs =
      (evaluate (zeros n) xorV gs cs).map (xorV seed) := by
  induction gs generalizing seed cs with
  | nil =>
      cases cs with
      | nil =>
          change some seed = some (xorV seed (zeros n))
          rw [← sw, xor_zero_right]
      | cons b bs => rfl
  | cons g gs ih =>
      have wg := width g (List.Mem.head gs)
      have wt : ∀ v, v ∈ gs → v.length = n := fun v hv => width v (List.Mem.tail g hv)
      cases cs with
      | nil => rfl
      | cons b bs =>
          cases b with
          | false =>
              have ht := ih wt seed sw bs
              change runCoefficients seed gs bs = _
              rw [ht]
              cases ev : evaluate (zeros n) xorV gs bs <;> rfl
          | true =>
              have hw : (xorV seed g).length = n :=
                Eq.trans (xor_length seed g (Eq.trans sw wg.symm)) sw
              have ht := ih wt (xorV seed g) hw bs
              change runCoefficients (xorV seed g) gs bs = _
              rw [ht]
              cases ev : evaluate (zeros n) xorV gs bs with
              | none => rfl
              | some v => exact congrArg some (xor_associative seed g v)

theorem zero_run_evaluate (n : Nat) (gs : List Bits)
    (width : ∀ g, g ∈ gs → g.length = n) (cs : List Bool) :
    runCoefficients (zeros n) gs cs = evaluate (zeros n) xorV gs cs := by
  rw [run_evaluate n gs width (zeros n) (zeros_length n) cs]
  cases ev : evaluate (zeros n) xorV gs cs with
  | none => rfl
  | some v =>
      change some (xorV (zeros n) v) = some v
      have wv := evaluate_width n gs width cs v ev
      rw [← wv, xor_zero_left]

theorem coefficients_iff_generated (n : Nat) (gs : List Bits)
    (width : ∀ g, g ∈ gs → g.length = n) (out : Bits) :
    (∃ cs, evaluate (zeros n) xorV gs cs = some out) ↔ Generated (zeros n) gs out := by
  constructor
  · intro ⟨cs, h⟩
    apply (run_iff_generated gs (zeros n) out).mp
    exact ⟨cs, Eq.trans (zero_run_evaluate n gs width cs) h⟩
  · intro h
    obtain ⟨cs, hc⟩ := (run_iff_generated gs (zeros n) out).mpr h
    exact ⟨cs, Eq.trans (zero_run_evaluate n gs width cs).symm hc⟩

theorem generated_in_span (n : Nat) (gs : List Bits)
    (width : ∀ g, g ∈ gs → g.length = n) (out : Bits)
    (h : Generated (zeros n) gs out) : Span (zeros n) xorV gs out := by
  obtain ⟨cs, hc⟩ := (coefficients_iff_generated n gs width out).mpr h
  exact evaluate_span (zeros n) xorV gs cs out hc

end AlexandriaComplexity.EnumerationBridge

import AlexandriaComplexity.SpanReduction

namespace AlexandriaComplexity.CoefficientChecker
open SpanReduction

def evaluate {A : Type} (z : A) (add : A → A → A)
    (basis : List A) (coeff : List Bool) : Option A :=
  match basis with
  | [] => match coeff with
    | [] => some z
    | _ :: _ => none
  | g :: gs => match coeff with
    | [] => none
    | bit :: bs => match evaluate z add gs bs with
      | none => none
      | some v => some (if bit then add g v else v)
termination_by structural basis

theorem evaluate_span {A : Type} (z : A) (add : A → A → A)
    (basis : List A) (coeff : List Bool) (x : A)
    (h : evaluate z add basis coeff = some x) : Span z add basis x := by
  induction basis generalizing coeff x with
  | nil =>
      cases coeff with
      | nil =>
          have hx : z = x := Option.some.inj h
          cases hx
          exact Span.zero
      | cons b bs => cases h
  | cons g gs ih =>
      cases coeff with
      | nil => cases h
      | cons bit bs =>
          cases ev : evaluate z add gs bs with
          | none =>
              change (match evaluate z add gs bs with
                | none => none | some v => some (if bit then add g v else v)) = some x at h
              rw [ev] at h
              cases h
          | some v =>
              have hv := ih bs v ev
              have hw : Span z add (g :: gs) v :=
                substitute_generators z add gs (g :: gs)
                  (fun y hy => Span.generator (List.Mem.tail g hy)) v hv
              change (match evaluate z add gs bs with
                | none => none | some v => some (if bit then add g v else v)) = some x at h
              rw [ev] at h
              cases bit with
              | false =>
                  have hx : v = x := Option.some.inj h
                  cases hx
                  exact hw
              | true =>
                  have hx : add g v = x := Option.some.inj h
                  cases hx
                  exact Span.combine (Span.generator (List.Mem.head gs)) hw

def checkCombination {A : Type} [DecidableEq A] (z : A) (add : A → A → A)
    (basis : List A) (coeff : List Bool) (x : A) : Bool :=
  decide (evaluate z add basis coeff = some x)

theorem checkCombination_sound {A : Type} [DecidableEq A]
    (z : A) (add : A → A → A) (basis : List A) (coeff : List Bool) (x : A)
    (h : checkCombination z add basis coeff x = true) : Span z add basis x :=
  evaluate_span z add basis coeff x (of_decide_eq_true h)

def checkRows {A : Type} [DecidableEq A] (z : A) (add : A → A → A)
    (basis targets : List A) (coefficients : List (List Bool)) : Bool :=
  match targets with
  | [] => match coefficients with
    | [] => true
    | _ :: _ => false
  | x :: xs => match coefficients with
    | [] => false
    | c :: cs => checkCombination z add basis c x && checkRows z add basis xs cs
termination_by structural targets

theorem checkRows_sound {A : Type} [DecidableEq A]
    (z : A) (add : A → A → A) (basis targets : List A)
    (coefficients : List (List Bool)) (h : checkRows z add basis targets coefficients = true) :
    ∀ x, x ∈ targets → Span z add basis x := by
  induction targets generalizing coefficients with
  | nil => intro x hx; cases hx
  | cons t ts ih =>
      cases coefficients with
      | nil => cases h
      | cons c cs =>
          have split : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
          have parts := split _ _ h
          intro x hx
          cases hx with
          | head => exact checkCombination_sound z add basis c t parts.1
          | tail _ hm => exact ih cs parts.2 x hm

def checkMutual {A : Type} [DecidableEq A] (z : A) (add : A → A → A)
    (source target : List A) (forward backward : List (List Bool)) : Bool :=
  checkRows z add source target forward && checkRows z add target source backward

theorem checkMutual_sound {A : Type} [DecidableEq A]
    (z : A) (add : A → A → A) (source target : List A)
    (forward backward : List (List Bool))
    (h : checkMutual z add source target forward backward = true) (x : A) :
    Span z add source x ↔ Span z add target x := by
  have split : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
  have parts := split _ _ h
  exact mutual_coverage z add source target
    (checkRows_sound z add target source backward parts.2)
    (checkRows_sound z add source target forward parts.1) x

theorem checked_predicate_preserved {A : Type} [DecidableEq A]
    (z : A) (add : A → A → A) (source target : List A)
    (forward backward : List (List Bool))
    (h : checkMutual z add source target forward backward = true) (accept : A → Prop) :
    (∃ x, Span z add source x ∧ accept x) ↔
    (∃ x, Span z add target x ∧ accept x) := by
  constructor
  · intro ⟨x, hs, ha⟩
    exact ⟨x, (checkMutual_sound z add source target forward backward h x).mp hs, ha⟩
  · intro ⟨x, ht, ha⟩
    exact ⟨x, (checkMutual_sound z add source target forward backward h x).mpr ht, ha⟩

end AlexandriaComplexity.CoefficientChecker

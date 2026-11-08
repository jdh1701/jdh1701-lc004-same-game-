import AlexandriaComplexity.GeneralResolution

namespace AlexandriaComplexity

/-!
A set-normalized presentation of propositional Resolution over the existing
list-clause semantics.

`sameClause` checks mutual Boolean inclusion. This makes clause order and
duplicate literals irrelevant while retaining explicit kernel-reduced evidence
for every initial clause, pivot, and resolvent. The soundness layer is generic;
concrete generated certificates live in separate modules.
-/

def containsLiteral (target : Literal) : Clause → Bool
  | [] => false
  | head :: tail =>
      if head = target then true else containsLiteral target tail

def clauseSubset (source target : Clause) : Bool :=
  match source with
  | [] => true
  | head :: tail =>
      containsLiteral head target && clauseSubset tail target

def sameClause (left right : Clause) : Bool :=
  clauseSubset left right && clauseSubset right left

def containsClause (target : Clause) : CNF → Bool
  | [] => false
  | head :: tail =>
      sameClause head target || containsClause target tail

theorem bool_and_left_true
    (left right : Bool)
    (bothTrue : (left && right) = true) :
    left = true := by
  cases left with
  | false =>
      contradiction
  | true =>
      rfl

theorem bool_and_right_true
    (left right : Bool)
    (bothTrue : (left && right) = true) :
    right = true := by
  cases right with
  | false =>
      cases left <;> contradiction
  | true =>
      rfl

theorem evalClause_containsLiteral_true
    (assignment : Assignment)
    (target : Literal)
    (clause : Clause)
    (present : containsLiteral target clause = true)
    (targetTrue : evalLiteral assignment target = true) :
    evalClause assignment clause = true := by
  induction clause with
  | nil =>
      change false = true at present
      contradiction
  | cons head tail inductionHypothesis =>
      rw [containsLiteral] at present
      by_cases equal : head = target
      · subst head
        change
          (evalLiteral assignment target || evalClause assignment tail) = true
        rw [targetTrue]
        rfl
      · rw [ite_eq_right equal] at present
        change
          (evalLiteral assignment head || evalClause assignment tail) = true
        have tailTrue : evalClause assignment tail = true :=
          inductionHypothesis present
        rw [tailTrue]
        cases evalLiteral assignment head <;> rfl

theorem evalClause_clauseSubset_true
    (assignment : Assignment)
    (source target : Clause)
    (subset : clauseSubset source target = true)
    (sourceTrue : evalClause assignment source = true) :
    evalClause assignment target = true := by
  induction source with
  | nil =>
      change false = true at sourceTrue
      contradiction
  | cons head tail inductionHypothesis =>
      rw [clauseSubset] at subset
      have headPresent : containsLiteral head target = true :=
        bool_and_left_true
          (containsLiteral head target)
          (clauseSubset tail target)
          subset
      have tailSubset : clauseSubset tail target = true :=
        bool_and_right_true
          (containsLiteral head target)
          (clauseSubset tail target)
          subset
      change
        (evalLiteral assignment head || evalClause assignment tail) = true
        at sourceTrue
      cases headValue : evalLiteral assignment head with
      | false =>
          rw [headValue] at sourceTrue
          rw [Bool.false_or] at sourceTrue
          exact inductionHypothesis tailSubset sourceTrue
      | true =>
          exact evalClause_containsLiteral_true assignment head target
            headPresent headValue

theorem evalCNF_containsClause_true
    (assignment : Assignment)
    (formula : CNF)
    (clause : Clause)
    (present : containsClause clause formula = true)
    (formulaTrue : evalCNF assignment formula = true) :
    evalClause assignment clause = true := by
  induction formula with
  | nil =>
      change false = true at present
      contradiction
  | cons head tail inductionHypothesis =>
      change
        (evalClause assignment head && evalCNF assignment tail) = true
        at formulaTrue
      have headTrue : evalClause assignment head = true :=
        bool_and_left_true
          (evalClause assignment head)
          (evalCNF assignment tail)
          formulaTrue
      have tailTrue : evalCNF assignment tail = true :=
        bool_and_right_true
          (evalClause assignment head)
          (evalCNF assignment tail)
          formulaTrue
      rw [containsClause] at present
      cases sameValue : sameClause head clause with
      | false =>
          rw [sameValue, Bool.false_or] at present
          exact inductionHypothesis present tailTrue
      | true =>
          unfold sameClause at sameValue
          have headSubset : clauseSubset head clause = true :=
            bool_and_left_true
              (clauseSubset head clause)
              (clauseSubset clause head)
              sameValue
          exact evalClause_clauseSubset_true assignment head clause
            headSubset headTrue

inductive SetResolutionDerivation (formula : CNF) : Clause → Prop where
  | initial
      (clause : Clause)
      (present : containsClause clause formula = true) :
      SetResolutionDerivation formula clause
  | resolve
      (pivot : Nat)
      (left right result : Clause)
      (leftHasPivot : containsLiteral (positiveLiteral pivot) left = true)
      (rightHasPivot : containsLiteral (negativeLiteral pivot) right = true)
      (sameResult : sameClause (generalResolvent pivot left right) result = true)
      (leftDerivation : SetResolutionDerivation formula left)
      (rightDerivation : SetResolutionDerivation formula right) :
      SetResolutionDerivation formula result

theorem set_resolution_derivation_sound
    (assignment : Assignment)
    (formula : CNF)
    (clause : Clause)
    (formulaTrue : evalCNF assignment formula = true)
    (derivation : SetResolutionDerivation formula clause) :
    evalClause assignment clause = true := by
  induction derivation with
  | initial clause present =>
      exact evalCNF_containsClause_true assignment formula clause
        present formulaTrue
  | resolve pivot left right result leftHasPivot rightHasPivot sameResult
      leftDerivation rightDerivation leftSound rightSound =>
      have rawTrue :
          evalClause assignment (generalResolvent pivot left right) = true :=
        general_resolution_step_sound assignment pivot left right
          leftSound rightSound
      have rawSubset :
          clauseSubset (generalResolvent pivot left right) result = true :=
        bool_and_left_true
          (clauseSubset (generalResolvent pivot left right) result)
          (clauseSubset result (generalResolvent pivot left right))
          sameResult
      exact evalClause_clauseSubset_true assignment
        (generalResolvent pivot left right) result rawSubset rawTrue

theorem set_resolution_refutation_unsat
    (formula : CNF)
    (refutation : SetResolutionDerivation formula []) :
    ¬ ∃ assignment, evalCNF assignment formula = true := by
  intro witness
  rcases witness with ⟨assignment, formulaTrue⟩
  have emptyTrue : evalClause assignment [] = true :=
    set_resolution_derivation_sound assignment formula [] formulaTrue refutation
  rw [empty_clause_is_false] at emptyTrue
  contradiction

end AlexandriaComplexity

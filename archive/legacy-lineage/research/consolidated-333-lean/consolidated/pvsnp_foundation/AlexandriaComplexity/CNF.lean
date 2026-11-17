namespace AlexandriaComplexity

/-- A Boolean literal with an explicit variable index and polarity. -/
structure Literal where
  index : Nat
  positive : Bool
deriving DecidableEq, Repr

/-- Total assignments make the C0 semantics independent of partial-map defaults. -/
abbrev Assignment := Nat → Bool

abbrev Clause := List Literal
abbrev CNF := List Clause

def evalLiteral (assignment : Assignment) (literal : Literal) : Bool :=
  match literal.positive with
  | true => assignment literal.index
  | false => Bool.not (assignment literal.index)

def evalClause (assignment : Assignment) (clause : Clause) : Bool :=
  clause.any (evalLiteral assignment)

def evalCNF (assignment : Assignment) (formula : CNF) : Bool :=
  formula.all (evalClause assignment)

/-- The explicit NP witness predicate at the Boolean-formula layer. -/
def verifyWitness (formula : CNF) (assignment : Assignment) : Bool :=
  evalCNF assignment formula

theorem verifier_sound (formula : CNF) (assignment : Assignment)
    (accepted : verifyWitness formula assignment = true) :
    evalCNF assignment formula = true := by
  exact accepted

theorem verifier_complete (formula : CNF) (assignment : Assignment)
    (satisfied : evalCNF assignment formula = true) :
    verifyWitness formula assignment = true := by
  exact satisfied

theorem empty_cnf_is_true (assignment : Assignment) :
    evalCNF assignment [] = true := by
  rfl

theorem empty_clause_is_false (assignment : Assignment) :
    evalClause assignment [] = false := by
  rfl

end AlexandriaComplexity

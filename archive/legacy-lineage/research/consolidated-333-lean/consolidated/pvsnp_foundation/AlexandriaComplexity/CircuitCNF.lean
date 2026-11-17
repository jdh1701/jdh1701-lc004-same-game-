namespace AlexandriaComplexity

/-!
Local Tseitin-style CNF gadgets for the Boolean circuit basis NOT, AND, and OR.
These truth-table theorems establish only gate-level semantic equivalence.  They
do not establish SAT hardness, a circuit lower bound, or P ≠ NP.
-/

def notGateCNF (a z : Bool) : Bool :=
  (Bool.not z || Bool.not a) && (z || a)

def andGateCNF (a b z : Bool) : Bool :=
  ((Bool.not z || a) && (Bool.not z || b)) &&
    (z || Bool.not a || Bool.not b)

def orGateCNF (a b z : Bool) : Bool :=
  ((z || Bool.not a) && (z || Bool.not b)) &&
    (Bool.not z || a || b)

theorem notGateCNF_correct (a z : Bool) :
    notGateCNF a z = true ↔ z = Bool.not a := by
  cases a <;> cases z <;> decide

theorem andGateCNF_correct (a b z : Bool) :
    andGateCNF a b z = true ↔ z = (a && b) := by
  cases a <;> cases b <;> cases z <;> decide

theorem orGateCNF_correct (a b z : Bool) :
    orGateCNF a b z = true ↔ z = (a || b) := by
  cases a <;> cases b <;> cases z <;> decide

end AlexandriaComplexity

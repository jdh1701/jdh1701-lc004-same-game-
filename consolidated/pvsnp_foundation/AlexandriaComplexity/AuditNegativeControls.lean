import Std

/- Deliberately untrusted audit fixtures. Not mathematical result targets.
The workflow MUST reject rejectedProof; its axiom is test input only. -/
namespace AlexandriaAuditControls

theorem acceptedProof : True := True.intro
axiom untrustedTestAxiom : False
theorem rejectedProof : False := untrustedTestAxiom
theorem rejectedExtensionality (P Q : Prop) (h : P ↔ Q) : P = Q := propext h
def rejectedDefinition : Nat := 0

end AlexandriaAuditControls

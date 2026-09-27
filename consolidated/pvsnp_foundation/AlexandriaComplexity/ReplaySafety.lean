/- A generic soundness obligation only. No graph implementation correspondence. -/
namespace AlexandriaReplay

theorem rechecked_counterexample_refutes {G : Type} (P Q : G → Prop)
    (g : G) (premise : P g) (counterexample : ¬ Q g) :
    ¬ (∀ x : G, P x → Q x) := by
  intro universal
  exact counterexample (universal g premise)

end AlexandriaReplay

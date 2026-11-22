import FiniteBlock
namespace LC004.RawGrowth

private abbrev ProperWords (n : ℕ) :=
  {f : Fin n → Fin 3 // FusionProper (List.ofFn f)}

private theorem extend_iff (n : ℕ) (a : Fin 3) (v : Fin (n+1) → Fin 3) :
    FusionProper (List.ofFn (Fin.cons a v)) ↔ a ≠ v 0 ∧ FusionProper (List.ofFn v) := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,FusionProper]
  have hh : (List.ofFn v).head? = some (v 0) := by rw [List.ofFn_succ]; rfl
  rw [hh]
  simp [ne_comm]

private def peel (n : ℕ) : ProperWords (n+2) ≃
    (Σ v : ProperWords (n+1), {a : Fin 3 // a ≠ v.val 0}) where
  toFun f := by
    let v := fun i : Fin (n+1) => f.val i.succ
    have eq : Fin.cons (f.val 0) v = f.val := Fin.cons_self_tail _
    have h := (extend_iff n (f.val 0) v).mp (eq.symm ▸ f.property)
    exact ⟨⟨v,h.2⟩,⟨f.val 0,h.1⟩⟩
  invFun p := ⟨Fin.cons p.2.val p.1.val,(extend_iff n _ _).mpr ⟨p.2.property,p.1.property⟩⟩
  left_inv f := Subtype.ext (Fin.cons_self_tail _)
  right_inv := by rintro ⟨⟨v,hv⟩,⟨a,ha⟩⟩; rfl

theorem proper_word_count (n : ℕ) : Nat.card (ProperWords (n+1)) = 3*2^n := by
  classical
  induction n with
  | zero =>
    let e : ProperWords 1 ≃ (Fin 1 → Fin 3) :=
      Equiv.subtypeUnivEquiv (fun f => by
        rw [List.ofFn_succ]; simp [FusionProper])
    simpa [Nat.card_fun] using Nat.card_congr e
  | succ n ih =>
    rw [Nat.card_congr (peel n),Nat.card_eq_fintype_card,Fintype.card_sigma]
    have h (v : ProperWords (n+1)) : Fintype.card {a : Fin 3 // a ≠ v.val 0} = 2 := by
      simp [Fintype.card_subtype_compl]
    simp_rw [h]
    simp [← Nat.card_eq_fintype_card,ih,pow_succ,Nat.mul_assoc]

/-- All proper ternary words of length 2H+1 are excluded, even when the
intermediate stacks inside each aligned block are unconstrained. -/
theorem capped_block_count_proper (H m : ℕ) :
    Nat.card {f : Fin m → (Fin (2*H+1) → Fin 3) //
      ∀ i, ∃ s t, s.length ≤ H ∧ t.length ≤ H ∧ FusionEval s (List.ofFn (f i)) t}
      ≤ (3^(2*H+1)-3*2^(2*H))^m := by
  classical
  let b := 2*H+1
  let P (u : Fin b → Fin 3) := FusionProper (List.ofFn u)
  let F (f : {f : Fin m → (Fin b → Fin 3) //
      ∀ i, ∃ s t, s.length ≤ H ∧ t.length ≤ H ∧ FusionEval s (List.ofFn (f i)) t}) :
      Fin m → {u : Fin b → Fin 3 // ¬ P u} := fun i => ⟨_,by
        intro hp
        obtain ⟨s,t,hs,ht,run⟩ := f.property i
        exact fixed_cap_forbids_segment H _ hp (by simp [b]) s t hs ht run⟩
  have inj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun g => (g i).val) h
  have h := Nat.card_le_card_of_injective F inj
  have c : Fintype.card {u // P u} = 3*2^(2*H) := by
    rw [← Nat.card_eq_fintype_card]
    exact proper_word_count (2*H)
  simpa [Nat.card_fun,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,c,b] using h

#print axioms capped_block_count_proper
end LC004.RawGrowth

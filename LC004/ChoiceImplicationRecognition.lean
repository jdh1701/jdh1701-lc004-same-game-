import LC004.FiveClassSplitPartitions

namespace LC004
open scoped Classical

def ChoiceImplicationEdge {ι : Type*} {D : ι → Type*}
    (C : ∀ i j, D i → D j → Prop) (a b : ∀ i, D i) (i j : ι) : Prop :=
  i ≠ j ∧ ¬ C i j (b i) (a j)

def ChoiceImplicationStrong {ι : Type*} {D : ι → Type*}
    (C : ∀ i j, D i → D j → Prop) (a b : ∀ i, D i) : Prop :=
  ∀ i j, Relation.ReflTransGen (ChoiceImplicationEdge C a b) i j

/-- Strong connectivity turns a separated pair into the entire solution set.
Only one row/column cover is needed to exclude values outside that pair. -/
theorem choice_pair_rigid_of_implication_strong {ι : Type*} {D : ι → Type*}
    [∀ i, DecidableEq (D i)] [DecidableEq (∀ i, D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ x, x ∈ A ↔ ∀ i j, i ≠ j → C i j (x i) (x j))
    (hclosed : ChoiceSolutionsClosed A) (a b : ∀ i, D i) (ha : a ∈ A) (hb : b ∈ A)
    (hsep : ∀ i, a i ≠ b i) (hsmall : ChoiceSmallEdge A)
    (hstrong : ChoiceImplicationStrong C a b) : A = {a,b} := by
  classical
  have hsub : ∀ c ∈ A, c = a ∨ c = b := by
    intro c hc
    have hB : ∀ i j, ChoiceImplicationEdge C a b i j → c i = b i → c j = b j := by
      intro i j he hci
      by_contra hne
      have hw := (hspec _).mp (hclosed a ha b hb c hc) i j he.1
      exact he.2 (by simpa [choiceMajority,hci,Ne.symm hne] using hw)
    have hA : ∀ i j, ChoiceImplicationEdge C a b i j → c j = a j → c i = a i := by
      intro i j he hcj
      by_contra hne
      have hw := (hspec _).mp (hclosed b hb a ha c hc) i j he.1
      exact he.2 (by simpa [choiceMajority,hcj,Ne.symm hne] using hw)
    have hpathB : ∀ i j, Relation.ReflTransGen (ChoiceImplicationEdge C a b) i j →
        c i = b i → c j = b j := by
      intro i j hp hi
      induction hp with
      | refl => exact hi
      | tail hp he ih => exact hB _ _ he ih
    have hpathA : ∀ i j, Relation.ReflTransGen (ChoiceImplicationEdge C a b) i j →
        c j = a j → c i = a i := by
      intro i j hp
      induction hp with
      | refl => exact id
      | tail hp he ih => exact fun hj => ih (hA _ _ he hj)
    have allA (i : ι) (hi : c i = a i) : c = a :=
      funext fun j => hpathA j i (hstrong j i) hi
    have allB (i : ι) (hi : c i = b i) : c = b :=
      funext fun j => hpathB i j (hstrong i j) hi
    obtain ⟨i,j,_,p,q,hcover⟩ := hsmall
    have hp : p = a i ∨ p = b i := by
      by_contra hn
      push_neg at hn
      have haj := (hcover a ha).resolve_left (fun h => hn.1 h.symm)
      have hbj := (hcover b hb).resolve_left (fun h => hn.2 h.symm)
      exact hsep j (haj.trans hbj.symm)
    have hq : q = a j ∨ q = b j := by
      by_contra hn
      push_neg at hn
      have hai := (hcover a ha).resolve_right (fun h => hn.1 h.symm)
      have hbi := (hcover b hb).resolve_right (fun h => hn.2 h.symm)
      exact hsep i (hai.trans hbi.symm)
    rcases hcover c hc with hci | hcj
    · rcases hp with hp | hp
      · exact Or.inl (allA i (hci.trans hp))
      · exact Or.inr (allB i (hci.trans hp))
    · rcases hq with hq | hq
      · exact Or.inl (allA j (hcj.trans hq))
      · exact Or.inr (allB j (hcj.trans hq))
  ext c
  constructor
  · intro hc
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hsub c hc
  · intro hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl <;> assumption

/-- If a separated pair is the entire binary solution family, every variable
must reach every other. A missing path constructs a third binary solution. -/
theorem choice_implication_strong_of_pair {ι : Type*} {D : ι → Type*}
    [DecidableEq (∀ i, D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ x, x ∈ A ↔ ∀ i j, i ≠ j → C i j (x i) (x j))
    (hsym : ∀ i j x y, C i j x y ↔ C j i y x)
    (a b : ∀ i, D i) (ha : a ∈ A) (hb : b ∈ A) (hsep : ∀ i, a i ≠ b i)
    (heq : A = {a,b}) : ChoiceImplicationStrong C a b := by
  classical
  intro i j
  by_contra hn
  let reach := Relation.ReflTransGen (ChoiceImplicationEdge C a b) i
  let c : ∀ l, D l := fun l => if reach l then b l else a l
  have hc : c ∈ A := by
    apply (hspec c).mpr
    intro u v huv
    by_cases hu : reach u <;> by_cases hv : reach v
    · simpa only [c,if_pos hu,if_pos hv] using (hspec b).mp hb u v huv
    · simp only [c,if_pos hu,if_neg hv]
      by_contra hbad
      exact hv (hu.tail ⟨huv,hbad⟩)
    · simp only [c,if_neg hu,if_pos hv]
      by_contra hbad
      have he : ChoiceImplicationEdge C a b v u :=
        ⟨Ne.symm huv,fun h => hbad ((hsym u v (a u) (b v)).mpr h)⟩
      exact hu (hv.tail he)
    · simpa only [c,if_neg hu,if_neg hv] using (hspec a).mp ha u v huv
  have hci : c i = b i := by simp only [c,reach,if_pos Relation.ReflTransGen.refl]
  have hcj : c j = a j := by simp only [c,reach,if_neg hn]
  rw [heq] at hc
  simp only [Finset.mem_insert,Finset.mem_singleton] at hc
  rcases hc with he | he
  · exact hsep i ((congrFun he i).symm.trans hci)
  · exact hsep j (hcj.symm.trans (congrFun he j))

/-- Polynomial-time recognition of a proposed separated surviving pair: local
compatibility plus one cover reduces uniqueness to directed strong connectivity.
Finding/enumerating the proposed pairs is a separate problem. -/
theorem choice_pair_rigid_iff_implication_strong {ι : Type*} {D : ι → Type*}
    [∀ i, DecidableEq (D i)] [DecidableEq (∀ i, D i)]
    (A : Finset (∀ i, D i)) (C : ∀ i j, D i → D j → Prop)
    (hspec : ∀ x, x ∈ A ↔ ∀ i j, i ≠ j → C i j (x i) (x j))
    (hsym : ∀ i j x y, C i j x y ↔ C j i y x)
    (hclosed : ChoiceSolutionsClosed A) (a b : ∀ i, D i) (ha : a ∈ A) (hb : b ∈ A)
    (hsep : ∀ i, a i ≠ b i) (hsmall : ChoiceSmallEdge A) :
    A = {a,b} ↔ ChoiceImplicationStrong C a b :=
  ⟨choice_implication_strong_of_pair A C hspec hsym a b ha hb hsep,
   choice_pair_rigid_of_implication_strong A C hspec hclosed a b ha hb hsep hsmall⟩

#print axioms choice_pair_rigid_iff_implication_strong
end LC004

import LC004.GrammarNormalForm
import Mathlib.Data.List.TakeDrop

namespace LC004

/-- Insert a word at a cell boundary; indices beyond the end append. -/
def spliceWord (i : Nat) (v w : List Nat) : List Nat :=
  w.take i ++ v ++ w.drop i

theorem spliceWord_cons (c i : Nat) (v w : List Nat) :
    spliceWord (i+1) v (c :: w) = c :: spliceWord i v w := by
  simp [spliceWord]

theorem spliceWord_end (i : Nat) (v w : List Nat) (h : w.length ≤ i) :
    spliceWord i v w = w ++ v := by
  simp [spliceWord, List.take_of_length_le h, List.drop_eq_nil_of_le h]

theorem spliceWord_append_left (i : Nat) (v u w : List Nat) (h : i ≤ u.length) :
    spliceWord i v (u ++ w) = spliceWord i v u ++ w := by
  simp [spliceWord, List.take_append_eq_append_take, List.drop_append_eq_append_drop, Nat.sub_eq_zero_of_le h,
    List.append_assoc]

theorem spliceWord_append_right (i : Nat) (v u w : List Nat) (h : u.length ≤ i) :
    spliceWord i v (u ++ w) = u ++ spliceWord (i-u.length) v w := by
  simp [spliceWord, List.take_append_eq_append_take, List.drop_append_eq_append_drop, List.take_of_length_le h,
    List.drop_eq_nil_of_le h, List.append_assoc]

/-- A grammar word can be inserted at any cell boundary of another one. -/
theorem clickGrammar_splice {w : List Nat} (hw : ClickGrammar w)
    (v : List Nat) (hv : ClickGrammar v) (i : Nat) :
    ClickGrammar (spliceWord i v w) := by
  induction hw generalizing i with
  | empty => simpa [spliceWord] using hv
  | @append u z hu hz ihu ihz =>
      by_cases hi : i ≤ u.length
      · rw [spliceWord_append_left i v u z hi]
        exact (ihu i).append hz
      · rw [spliceWord_append_right i v u z (by omega)]
        exact hu.append (ihz (i-u.length))
  | @pair c u hu ihu =>
      cases i with
      | zero => simpa [spliceWord] using hv.append (ClickGrammar.pair c hu)
      | succ i =>
          by_cases hi : i ≤ u.length
          · rw [spliceWord_cons, spliceWord_append_left i v u [c] hi]
            exact ClickGrammar.pair c (ihu i)
          · rw [spliceWord_end _ _ _ (by simp; omega)]
            exact (ClickGrammar.pair c hu).append hv
  | @triple c u z hu hz ihu ihz =>
      cases i with
      | zero => simpa [spliceWord] using hv.append (ClickGrammar.triple c hu hz)
      | succ i =>
          by_cases hi : i ≤ u.length
          · rw [spliceWord_cons, spliceWord_append_left i v u _ hi]
            exact ClickGrammar.triple c (ihu i) hz
          · obtain ⟨k, hk⟩ : ∃ k, i = u.length + (k+1) := by
              exact ⟨i-u.length-1, by omega⟩
            by_cases hki : k ≤ z.length
            · rw [spliceWord_cons, spliceWord_append_right i v u _ (by omega), hk]
              simp only [Nat.add_sub_cancel_left, spliceWord_cons]
              rw [spliceWord_append_left k v z [c] hki]
              exact ClickGrammar.triple c hu (ihz k)
            · rw [spliceWord_end _ _ _ (by simp; omega)]
              exact (ClickGrammar.triple c hu hz).append hv

theorem clickGrammar_insert {u v : List Nat} (h : ClickGrammar (u ++ v))
    {z : List Nat} (hz : ClickGrammar z) : ClickGrammar (u ++ z ++ v) := by
  simpa [spliceWord] using clickGrammar_splice h z hz u.length

/-- Every monochromatic word of at least two cells belongs to the grammar. -/
theorem clickGrammar_replicate (c n : Nat) (hn : 2 ≤ n) :
    ClickGrammar (List.replicate n c) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h2 : n = 2
      · subst n
        exact ClickGrammar.pair c ClickGrammar.empty
      by_cases h3 : n = 3
      · subst n
        exact ClickGrammar.triple c ClickGrammar.empty ClickGrammar.empty
      have hsmall : n - 2 < n := by omega
      have hlarge : 2 ≤ n - 2 := by omega
      have hp := ClickGrammar.pair c (ih (n-2) hsmall hlarge)
      have he : n = (n-2)+1+1 := by omega
      have heq := congrArg (fun k => List.replicate k c) he
      dsimp only at heq
      rw [List.replicate_succ, List.replicate_succ'] at heq
      rw [heq]
      exact hp

#print axioms clickGrammar_splice
#print axioms clickGrammar_insert
#print axioms clickGrammar_replicate

end LC004

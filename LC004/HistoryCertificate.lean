import LC004.CertificateInsertion
import LC004.ReverseInsertionHistory

namespace LC004

/-- Certificates refer to the actual colors of the original word. -/
def HasNoncrossing23Certificate {q : Nat} (w : List (Fin q)) : Prop :=
  Nonempty (Noncrossing23Certificate w.get)

/-- Read the enlarged word using the length n+k expected by insertion. -/
def insertedWordColor {q : Nat} (left right : List (Fin q))
    (a : Fin q) (k : Nat) :
    Fin ((left ++ right).length + k) → Fin q :=
  fun i => (left ++ List.replicate k a ++ right).get
    ⟨i.val, by
      have hi := i.isLt
      simp only [List.length_append, List.length_replicate] at *
      omega⟩

theorem insertedWordColor_old {q : Nat} (left right : List (Fin q))
    (a : Fin q) (k : Nat) (i : Fin (left ++ right).length) :
    insertedWordColor left right a k (oldPosition left.length k i) =
      (left ++ right).get i := by
  simp only [insertedWordColor, oldPosition, List.get_eq_getElem]
  by_cases hi : i.val < left.length
  · simp [shiftAfterInsertion, hi, List.getElem_append]
  · have h1 : ¬ i.val + k < left.length := by omega
    have h2 : ¬ i.val + k - left.length < k := by omega
    have h3 : i.val + k - left.length - k = i.val - left.length := by omega
    simp [shiftAfterInsertion, hi, List.getElem_append, h1, h2, h3]

theorem insertedWordColor_fresh {q : Nat} (left right : List (Fin q))
    (a : Fin q) (k : Nat) (s : Fin k) :
    insertedWordColor left right a k
      (freshPosition left.length k (by simp) s) = a := by
  have hs := s.isLt
  have h1 : ¬ left.length + s.val < left.length := by omega
  have h2 : left.length + s.val - left.length = s.val := by omega
  simp [insertedWordColor, freshPosition, List.getElem_append, h1, h2, hs]

/-- Transport a bounded certificate across an equality of word lengths. -/
theorem certificate_of_length_cast {m n q : Nat} (h : m = n)
    (color : Fin m → Fin q)
    (cert : Noncrossing23Certificate
      (fun i : Fin n => color (Fin.cast h.symm i))) :
    Nonempty (Noncrossing23Certificate color) := by
  subst n
  exact ⟨cert⟩

theorem has_certificate_empty (q : Nat) :
    HasNoncrossing23Certificate ([] : List (Fin q)) := by
  refine ⟨{ blocks := [], sizes := ?_, exactCover := ?_,
    monochromatic := ?_, noncrossing := ?_ }⟩
  · simp
  · exact List.Perm.refl []
  · simp
  · intro b hb
    simp at hb

/-- Certificate construction for a contextual pair/triple insertion. -/
theorem has_certificate_insert {q : Nat} (left right : List (Fin q))
    (a : Fin q) (k : Nat) (hk : k = 2 ∨ k = 3)
    (h : HasNoncrossing23Certificate (left ++ right)) :
    HasNoncrossing23Certificate (left ++ List.replicate k a ++ right) := by
  obtain ⟨cert⟩ := h
  have ci := cert.insert left.length k (by simp) hk
    (insertedWordColor left right a k) a
    (insertedWordColor_old left right a k)
    (insertedWordColor_fresh left right a k)
  have hlen : (left ++ List.replicate k a ++ right).length =
      (left ++ right).length + k := by simp; omega
  exact certificate_of_length_cast hlen
    (left ++ List.replicate k a ++ right).get ci

/-- Every reverse insertion history yields a full partition of the
original positions, rather than only a noncrossing family. -/
theorem insertion_history_to_certificate {q : Nat} {w : List (Fin q)}
    (h : InsertionHistory w) : HasNoncrossing23Certificate w := by
  induction h with
  | empty => exact has_certificate_empty q
  | pair left right a smaller ih =>
      simpa [List.replicate_succ] using
        has_certificate_insert left right a 2 (Or.inl rfl) ih
  | triple left right a smaller ih =>
      simpa [List.replicate_succ] using
        has_certificate_insert left right a 3 (Or.inr rfl) ih

theorem erases_empty_to_certificate {q : Nat} {w : List (Fin q)}
    (h : Erases w []) : HasNoncrossing23Certificate w :=
  insertion_history_to_certificate (erases_empty_to_insertion_history h)

/-- One direction of the proposed Same Game characterization, for
genuine maximal-run-winning words and arbitrary finite alphabets. -/
theorem raw_max_win_to_certificate {q : Nat} {w : List (Fin q)}
    (h : RawMaxErases w []) : HasNoncrossing23Certificate w :=
  insertion_history_to_certificate (raw_max_win_to_insertion_history h)

#print axioms insertion_history_to_certificate
#print axioms erases_empty_to_certificate
#print axioms raw_max_win_to_certificate

end LC004

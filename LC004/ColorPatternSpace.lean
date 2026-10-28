import LC004.RawCertificateEquivalence

namespace LC004

/-- A pattern records exactly which original positions have equal colors.
There are no color labels or orderings of color classes in this space. -/
abbrev ColorPattern (n : Nat) := Setoid (Fin n)

instance colorPatternFinite (n : Nat) : Finite (ColorPattern n) := by
  classical
  exact Finite.of_injective (fun p : ColorPattern n => p.r)
    (fun p q h => Setoid.ext fun i j => by rw [h])

noncomputable instance colorPatternFintype (n : Nat) : Fintype (ColorPattern n) :=
  Fintype.ofFinite _

def colorPatternOf {n q : Nat} (color : Fin n → Fin q) : ColorPattern n :=
  Setoid.ker color

/-- A representative position serves as the label of its color class.
This works also for n=0 and introduces no unused-label multiplicity. -/
noncomputable def patternColor {n : Nat} (p : ColorPattern n) (i : Fin n) : Fin n :=
  (Quotient.mk p i).out

theorem patternColor_eq_iff {n : Nat} (p : ColorPattern n) (i j : Fin n) :
    patternColor p i = patternColor p j ↔ p i j := by
  constructor
  · intro h
    apply Quotient.exact
    calc
      Quotient.mk p i = Quotient.mk p (patternColor p i) :=
        (Quotient.out_eq (Quotient.mk p i)).symm
      _ = Quotient.mk p (patternColor p j) := congrArg (Quotient.mk p) h
      _ = Quotient.mk p j := Quotient.out_eq (Quotient.mk p j)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

theorem colorPatternOf_patternColor {n : Nat} (p : ColorPattern n) :
    colorPatternOf (patternColor p) = p := by
  apply Setoid.ext
  intro i j
  exact patternColor_eq_iff p i j

theorem colorPatternOf_surjective (n : Nat) :
    Function.Surjective (@colorPatternOf n n) :=
  fun p => ⟨patternColor p, colorPatternOf_patternColor p⟩

/-- Certificates can be recolored whenever equal original colors stay
 equal. No globally defined renaming of unused alphabet symbols is needed. -/
def Noncrossing23Certificate.recolor {n q r : Nat}
    {color : Fin n → Fin q} (cert : Noncrossing23Certificate color)
    (target : Fin n → Fin r)
    (heq : ∀ i j, color i = color j → target i = target j) :
    Noncrossing23Certificate target where
  blocks := cert.blocks
  sizes := cert.sizes
  exactCover := cert.exactCover
  noncrossing := cert.noncrossing
  monochromatic := by
    intro b hb
    have hne : b ≠ [] := by
      have hs := cert.sizes b hb
      intro h
      simp [h] at hs
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil b hne
    obtain ⟨a, ha⟩ := cert.monochromatic b hb
    exact ⟨target i, fun j hj => heq j i ((ha j hj).trans (ha i hi).symm)⟩

theorem certificate_iff_same_color_pattern {n q r : Nat}
    (color : Fin n → Fin q) (target : Fin n → Fin r)
    (h : colorPatternOf color = colorPatternOf target) :
    Nonempty (Noncrossing23Certificate color) ↔
      Nonempty (Noncrossing23Certificate target) := by
  have heq (i j : Fin n) : color i = color j ↔ target i = target j := by
    change (colorPatternOf color) i j ↔ (colorPatternOf target) i j
    rw [h]
  exact ⟨fun ⟨c⟩ => ⟨c.recolor target (fun i j => (heq i j).mp)⟩,
    fun ⟨c⟩ => ⟨c.recolor color (fun i j => (heq i j).mpr)⟩⟩

theorem certificate_cast_iff {m n q : Nat} (h : m = n) (color : Fin n → Fin q) :
    Nonempty (Noncrossing23Certificate (fun i : Fin m => color (Fin.cast h i))) ↔
      Nonempty (Noncrossing23Certificate color) := by
  subst n
  rfl

theorem certificate_ofFn_iff {n q : Nat} (color : Fin n → Fin q) :
    HasNoncrossing23Certificate (List.ofFn color) ↔
      Nonempty (Noncrossing23Certificate color) := by
  have h : (List.ofFn color).length = n := List.length_ofFn
  have hc : (List.ofFn color).get =
      (fun i => color (Fin.cast h i)) := by
    funext i
    simp [List.get_ofFn]
  unfold HasNoncrossing23Certificate
  rw [hc]
  exact certificate_cast_iff h color

/-- This is the genuine game's winning condition on an unlabeled pattern. -/
def WinningColorPattern {n : Nat} (p : ColorPattern n) : Prop :=
  Nonempty (Noncrossing23Certificate (patternColor p))

theorem winning_color_pattern_iff_certificate {n q : Nat}
    (color : Fin n → Fin q) :
    WinningColorPattern (colorPatternOf color) ↔
      Nonempty (Noncrossing23Certificate color) := by
  exact certificate_iff_same_color_pattern _ _ (colorPatternOf_patternColor _)

theorem winning_color_pattern_iff_raw_win {n q : Nat}
    (color : Fin n → Fin q) :
    WinningColorPattern (colorPatternOf color) ↔
      RawMaxErases (List.ofFn color) [] := by
  rw [winning_color_pattern_iff_certificate,
    raw_max_win_iff_certificate, certificate_ofFn_iff]

theorem winning_word_pattern_iff {q : Nat} (w : List (Fin q)) :
    WinningColorPattern (colorPatternOf w.get) ↔ RawMaxErases w [] := by
  simpa only [List.ofFn_get] using winning_color_pattern_iff_raw_win w.get

/-- Number of used colors, intrinsically defined without alphabet labels. -/
def colorPatternClassCount {n : Nat} (p : ColorPattern n) : Nat :=
  Nat.card (Quotient p)

theorem colorPatternClassCount_of {n q : Nat} (color : Fin n → Fin q) :
    colorPatternClassCount (colorPatternOf color) = (List.ofFn color).toFinset.card := by
  classical
  let e : Set.range color ≃ {a : Fin q // a ∈ (List.ofFn color).toFinset} :=
    { toFun := fun a => ⟨a.val, by
        simpa only [List.mem_toFinset, List.mem_ofFn] using a.property⟩
      invFun := fun a => ⟨a.val, by
        simpa only [List.mem_toFinset, List.mem_ofFn] using a.property⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  calc
    _ = Nat.card (Set.range color) := Nat.card_congr (Setoid.quotientKerEquivRange color)
    _ = Nat.card {a : Fin q // a ∈ (List.ofFn color).toFinset} := Nat.card_congr e
    _ = _ := Nat.card_eq_finsetCard _

theorem colorPatternClassCount_word {q : Nat} (w : List (Fin q)) :
    colorPatternClassCount (colorPatternOf w.get) = w.toFinset.card := by
  simpa only [List.ofFn_get] using colorPatternClassCount_of w.get

/-- A precise finite target for A(n,k); no enumeration formula is asserted. -/
noncomputable def winningColorPatternCount (n k : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n //
    WinningColorPattern p ∧ colorPatternClassCount p = k}

/-- Perfect matchings use the same unlabeled pattern space, with each
class of size two and the usual alternating-endpoint exclusion. -/
def NoncrossingPairPattern {n : Nat} (p : ColorPattern n) : Prop :=
  (∀ i : Fin n, Nat.card {j : Fin n // p i j} = 2) ∧
  ∀ a b c d : Fin n, a < b → b < c → c < d → ¬ (p a c ∧ p b d)

noncomputable def noncrossingPairPatternCount (n : Nat) : Nat := by
  classical
  exact Fintype.card {p : ColorPattern n // NoncrossingPairPattern p}

#print axioms colorPatternOf_surjective
#print axioms certificate_iff_same_color_pattern
#print axioms winning_word_pattern_iff
#print axioms colorPatternClassCount_word

end LC004

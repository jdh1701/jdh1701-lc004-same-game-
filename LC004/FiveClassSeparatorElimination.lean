import LC004.ExclusiveSeparatorElimination
import LC004.ClassCutSeparators
import LC004.FiveClassSeparators
import LC004.LocalCertificateCatalogues

namespace LC004
open scoped Classical BigOperators

/-- Extend a cut on an embedded five-point class constantly outside the class. -/
noncomputable def selectedFiveCutBit {n : Nat} (e : Fin 5 ↪o Fin n)
    (t : FiveCut) (x : Fin n) : Bool :=
  if h : ∃ u, e u = x then fiveCutBit t (Classical.choose h) else false

@[simp] theorem selectedFiveCutBit_on {n : Nat} (e : Fin 5 ↪o Fin n)
    (t : FiveCut) (u : Fin 5) : selectedFiveCutBit e t (e u) = fiveCutBit t u := by
  have hh : ∃ v, e v = e u := ⟨u,rfl⟩
  have he : Classical.choose hh = u := e.injective (Classical.choose_spec hh)
  simp only [selectedFiveCutBit,dif_pos hh,he]

@[simp] theorem selectedFiveCutBit_off {n : Nat} (e : Fin 5 ↪o Fin n)
    (t : FiveCut) (x : Fin n) (hx : ¬ ∃ u, e u = x) : selectedFiveCutBit e t x = false := by
  simp only [selectedFiveCutBit,dif_neg hx]

noncomputable def selectedFiveCut {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) (t : FiveCut) : ColorPattern n :=
  p ⊓ Setoid.ker (selectedFiveCutBit e t)

noncomputable def selectedFiveCuts {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) : Finset (ColorPattern n) :=
  Finset.univ.image (selectedFiveCut p e)

/-- Only the relation on the designated class determines whether a refining
certificate lies below its cut. Saturation prevents a relation from crossing
the boundary of that class. -/
theorem le_selectedFiveCut_iff {n : Nat} (p c : ColorPattern n)
    (e : Fin 5 ↪o Fin n) (t : FiveCut) (hcp : c ≤ p)
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x) :
    c ≤ selectedFiveCut p e t ↔
      ∀ u v, c (e u) (e v) → fiveCutBit t u = fiveCutBit t v := by
  constructor
  · intro h u v huv
    have hh := (h huv).2
    change selectedFiveCutBit e t (e u) = selectedFiveCutBit e t (e v) at hh
    simpa using hh
  · intro h x y hxy
    refine ⟨hcp hxy,?_⟩
    change selectedFiveCutBit e t x = selectedFiveCutBit e t y
    by_cases hx : ∃ u, e u = x
    · obtain ⟨u,rfl⟩ := hx
      obtain ⟨v,rfl⟩ := hsat u y (hcp hxy)
      simpa using h u v hxy
    · have hy : ¬ ∃ v, e v = y := by
        rintro ⟨v,rfl⟩
        exact hx (hsat v x (hcp (c.symm hxy)))
      simp only [selectedFiveCutBit_off e t x hx,selectedFiveCutBit_off e t y hy]

theorem selectedFiveCut_strict {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) (hsame : ∀ u v, p (e u) (e v)) (t : FiveCut) :
    selectedFiveCut p e t < p := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  obtain ⟨u,v,huv⟩ := fiveCut_nonconstant t
  have hh := (Setoid.ext_iff.mp he (e u) (e v)).mpr (hsame u v)
  have hb := hh.2
  change selectedFiveCutBit e t (e u) = selectedFiveCutBit e t (e v) at hb
  exact huv (by simpa using hb)

theorem selectedFiveCuts_subset_proper {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) (hsame : ∀ u v, p (e u) (e v)) :
    selectedFiveCuts p e ⊆ properRefinements p := by
  intro v hv
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hv
  simpa only [properRefinements,Finset.mem_filter,Finset.mem_univ,true_and] using
    selectedFiveCut_strict p e hsame t

/-- Each actual local certificate on five points has exactly one possible
proper two-part coarsening. This finite lemma uses the COMPLETE local catalogue. -/
theorem localNC5_cut_unique : ∀ s : Fin 5, ∀ t u : FiveCut,
    (∀ a b, localNC5Color s a = localNC5Color s b → fiveCutBit t a = fiveCutBit t b) →
    (∀ a b, localNC5Color s a = localNC5Color s b → fiveCutBit u a = fiveCutBit u b) → t = u := by
  decide +kernel

/-- Exclusivity is now proved from original certificates, rather than assumed
as a property of an abstract choice complex. Other class sizes are unrestricted. -/
theorem original_certificate_five_cuts_exclusive {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x)
    (c : ColorPattern n) (hc : CertificateConstraint c) (hcp : c ≤ p)
    (a b : ColorPattern n) (ha : a ∈ selectedFiveCuts p e)
    (hb : b ∈ selectedFiveCuts p e) (hca : c ≤ a) (hcb : c ≤ b) : a = b := by
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hb
  have hres := certificateConstraint_restrict c hc e
    (fun i x h => hsat i x (hcp h))
  obtain ⟨s,hs⟩ := localNC5_pattern_complete _ hres.1 hres.2
  have hrel (i j : Fin 5) : c (e i) (e j) ↔ localNC5Color s i = localNC5Color s j :=
    (restrictColorPattern_rel c e i j).symm.trans (Setoid.ext_iff.mp hs i j)
  have ht := (le_selectedFiveCut_iff p c e t hcp hsat).mp hca
  have hu := (le_selectedFiveCut_iff p c e u hcp hsat).mp hcb
  have he : t = u := localNC5_cut_unique s t u
    (fun i j h => ht i j ((hrel i j).mpr h))
    (fun i j h => hu i j ((hrel i j).mpr h))
  exact congrArg (selectedFiveCut p e) he

/-- Eliminate the designated five-point class from any complete separating
family. The rest of the pattern may have arbitrary class sizes and crossings. -/
theorem winningJoinCoefficient_five_class_elimination {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x)
    (V : Finset (ColorPattern n))
    (hproper : ∀ v ∈ V, v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ v) :
    let F := facetFaces (certificateCoarseningFacets p V)
    winningJoinCoefficient n p =
      faceAlternatingSum (avoidMarkedFaces F (selectedFiveCuts p e)) -
        ∑ v ∈ selectedFiveCuts p e, faceAlternatingSum (separatorLink F v) := by
  apply winningJoinCoefficient_eliminate_exclusive p V (selectedFiveCuts p e) id hproper hcover
  exact fun c hc hcp a ha b hb hca hcb =>
    original_certificate_five_cuts_exclusive p e hsat c hc hcp a b ha hb hca hcb

/-- An unconditional choice of the separating family closes the formula for
every original pattern with a saturated ordered five-point subset. -/
theorem winningJoinCoefficient_five_class_elimination_canonical {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x) :
    let F := facetFaces (certificateCoarseningFacets p (properRefinements p))
    winningJoinCoefficient n p =
      faceAlternatingSum (avoidMarkedFaces F (selectedFiveCuts p e)) -
        ∑ v ∈ selectedFiveCuts p e, faceAlternatingSum (separatorLink F v) := by
  apply winningJoinCoefficient_five_class_elimination p e hsat
  · intro v hv
    simpa only [properRefinements,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  · intro q hqp hne
    exact ⟨q,by simp [properRefinements,lt_of_le_of_ne hqp hne],le_rfl⟩

/-- The five cuts compatible with a noncrossing pair/triple partition of a
five-point ordered class. The ten other cuts never occur in a certificate facet. -/
def activeFiveCut (s : Fin 5) : FiveCut := Sum.inr (![9,7,0,4,3] s)

theorem activeFiveCut_injective : Function.Injective activeFiveCut := by decide +kernel

theorem localNC5_cut_exact : ∀ s : Fin 5, ∀ t : FiveCut,
    (∀ u v, localNC5Color s u = localNC5Color s v → fiveCutBit t u = fiveCutBit t v) ↔
      t = activeFiveCut s := by decide +kernel

noncomputable def selectedFiveActiveCuts {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) : Finset (ColorPattern n) :=
  Finset.univ.image (fun s => selectedFiveCut p e (activeFiveCut s))

theorem selectedFiveActiveCuts_subset {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) : selectedFiveActiveCuts p e ⊆ selectedFiveCuts p e := by
  intro v hv
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨activeFiveCut s,Finset.mem_univ _,rfl⟩

theorem selectedFiveActiveCut_injective {n : Nat} (p : ColorPattern n)
    (e : Fin 5 ↪o Fin n) (hsame : ∀ u v, p (e u) (e v)) :
    Function.Injective (fun s => selectedFiveCut p e (activeFiveCut s)) := by
  intro a b he
  change selectedFiveCut p e (activeFiveCut a) = selectedFiveCut p e (activeFiveCut b) at he
  have ha := (localNC5_cut_exact a (activeFiveCut a)).mpr rfl
  have hb : ∀ u v, localNC5Color a u = localNC5Color a v →
      fiveCutBit (activeFiveCut b) u = fiveCutBit (activeFiveCut b) v := by
    intro u v huv
    have hc : selectedFiveCut p e (activeFiveCut a) (e u) (e v) := by
      refine ⟨hsame u v,?_⟩
      change selectedFiveCutBit e (activeFiveCut a) (e u) =
        selectedFiveCutBit e (activeFiveCut a) (e v)
      simpa using ha u v huv
    rw [he] at hc
    have hd := hc.2
    change selectedFiveCutBit e (activeFiveCut b) (e u) =
      selectedFiveCutBit e (activeFiveCut b) (e v) at hd
    simpa using hd
  exact activeFiveCut_injective ((localNC5_cut_exact a (activeFiveCut b)).mp hb).symm

/-- Every original certificate has a unique row, obtained from its ordered
restriction to the selected five-point class. -/
theorem original_certificate_unique_five_row {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x)
    (c : ColorPattern n) (hc : CertificateConstraint c) (hcp : c ≤ p) :
    ∃! s : Fin 5, c ≤ selectedFiveCut p e (activeFiveCut s) := by
  have hres := certificateConstraint_restrict c hc e
    (fun i x h => hsat i x (hcp h))
  obtain ⟨s,hs⟩ := localNC5_pattern_complete _ hres.1 hres.2
  have hrel (i j : Fin 5) : c (e i) (e j) ↔ localNC5Color s i = localNC5Color s j :=
    (restrictColorPattern_rel c e i j).symm.trans (Setoid.ext_iff.mp hs i j)
  refine ⟨s,?_,?_⟩
  · apply (le_selectedFiveCut_iff p c e (activeFiveCut s) hcp hsat).mpr
    intro i j hij
    exact (localNC5_cut_exact s (activeFiveCut s)).mpr rfl i j ((hrel i j).mp hij)
  · intro t ht
    have hcut := (le_selectedFiveCut_iff p c e (activeFiveCut t) hcp hsat).mp ht
    have he := (localNC5_cut_exact s (activeFiveCut t)).mp
      (fun i j h => hcut i j ((hrel i j).mpr h))
    exact activeFiveCut_injective he

/-- The exact five-row formula for an original five-point class. There is one
projection term and precisely five link terms; all other classes are arbitrary. -/
theorem winningJoinCoefficient_five_row_formula {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsame : ∀ u v, p (e u) (e v))
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x)
    (V : Finset (ColorPattern n))
    (hproper : ∀ v ∈ V, v < p)
    (hcover : ∀ q, q ≤ p → q ≠ p → ∃ v ∈ V, q ≤ v) :
    let F := facetFaces (certificateCoarseningFacets p V)
    winningJoinCoefficient n p =
      faceAlternatingSum (avoidMarkedFaces F (selectedFiveActiveCuts p e)) -
        ∑ s : Fin 5, faceAlternatingSum (separatorLink F (selectedFiveCut p e (activeFiveCut s))) := by
  classical
  dsimp only
  have h := winningJoinCoefficient_eliminate_exclusive p V (selectedFiveActiveCuts p e) id
    hproper hcover (fun c hc hcp a ha b hb hca hcb =>
      original_certificate_five_cuts_exclusive p e hsat c hc hcp a b
        (selectedFiveActiveCuts_subset p e ha) (selectedFiveActiveCuts_subset p e hb) hca hcb)
  dsimp only at h
  rw [selectedFiveActiveCuts,Finset.sum_image
    (fun _ _ _ _ he => selectedFiveActiveCut_injective p e hsame he)] at h
  exact h

/-- A canonical classwise binary-cut family discharges both separator
hypotheses in the five-row law for every original mixed pattern. -/
theorem winningJoinCoefficient_five_rows_class_cuts {n : Nat}
    (p : ColorPattern n) (e : Fin 5 ↪o Fin n)
    (hsame : ∀ u v, p (e u) (e v))
    (hsat : ∀ u x, p (e u) x → ∃ v, e v = x) :
    let F := facetFaces (certificateCoarseningFacets p (classCutSeparators p))
    winningJoinCoefficient n p =
      faceAlternatingSum (avoidMarkedFaces F (selectedFiveActiveCuts p e)) -
        ∑ s : Fin 5, faceAlternatingSum (separatorLink F (selectedFiveCut p e (activeFiveCut s))) :=
  winningJoinCoefficient_five_row_formula p e hsame hsat (classCutSeparators p)
    (classCutSeparators_strict p) (classCutSeparators_cover p)

#print axioms winningJoinCoefficient_five_rows_class_cuts
#print axioms original_certificate_unique_five_row
#print axioms winningJoinCoefficient_five_row_formula
#print axioms original_certificate_five_cuts_exclusive
#print axioms winningJoinCoefficient_five_class_elimination_canonical
end LC004

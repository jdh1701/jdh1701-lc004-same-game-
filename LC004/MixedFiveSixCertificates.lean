import LC004.MixedFiveSixGeometry
import LC004.LocalGeneratorTransfer

namespace LC004

/-- Every local combination has class sizes 2/3 and refines the original pattern;
noncrossing is the only remaining certificate condition. -/
theorem mixed56_encoded_sizes : ∀ s : Fin 5, ∀ t : Fin 8, ∀ u : Fin 11,
    (Finset.univ.filter (fun v => mixed56Color s t u = mixed56Color s t v)).card = 2 ∨
    (Finset.univ.filter (fun v => mixed56Color s t u = mixed56Color s t v)).card = 3 := by
  decide +kernel

theorem mixed56_encoded_refines : ∀ s : Fin 5, ∀ t : Fin 8, ∀ u v : Fin 11,
    mixed56Color s t u = mixed56Color s t v → mixed56BaseColor u = mixed56BaseColor v := by
  decide +kernel

theorem mixed56_encoded_certificate (s : Fin 5) (t : Fin 8)
    (h : Mixed56Compatible s t) :
    CertificateConstraint (mixed56Encoded s t) ∧ mixed56Encoded s t ≤ mixed56Pattern := by
  constructor
  · constructor
    · intro u
      have he : patternClassPositions (mixed56Encoded s t) u =
          Finset.univ.filter (fun v => mixed56Color s t u = mixed56Color s t v) := by
        ext v
        simp only [patternClassPositions,Finset.mem_filter,Finset.mem_univ,true_and]
        rfl
      rw [he]
      exact mixed56_encoded_sizes s t u
    · exact h
  · exact mixed56_encoded_refines s t

/-- The local catalogues exhaust every ORIGINAL certificate refining the mixed
pattern. Completeness is obtained by saturated ordered restrictions, not by
assuming that the displayed examples are all the certificates. -/
theorem mixed56_certificate_encoded (c : ColorPattern 11)
    (hc : CertificateConstraint c) (hcp : c ≤ mixed56Pattern) :
    ∃ s : Fin 5, ∃ t : Fin 8, c = mixed56Encoded s t := by
  have hL := certificateConstraint_restrict c hc mixed56Left
    (fun u x h => mixed56_left_saturated u x (hcp h))
  have hR := certificateConstraint_restrict c hc mixed56Right
    (fun u x h => mixed56_right_saturated u x (hcp h))
  obtain ⟨s,hs⟩ := localNC5_pattern_complete _ hL.1 hL.2
  obtain ⟨t,ht⟩ := localNC6_pattern_complete _ hR.1 hR.2
  refine ⟨s,t,Setoid.ext (fun x y => ?_)⟩
  have hl (u v : Fin 5) : c (mixed56Left u) (mixed56Left v) ↔
      localNC5Color s u = localNC5Color s v := by
    exact ((restrictColorPattern_rel c mixed56Left u v).symm).trans
      (Setoid.ext_iff.mp hs u v)
  have hr (u v : Fin 6) : c (mixed56Right u) (mixed56Right v) ↔
      localNC6Color t u = localNC6Color t v := by
    exact ((restrictColorPattern_rel c mixed56Right u v).symm).trans
      (Setoid.ext_iff.mp ht u v)
  rcases mixed56_cover x with ⟨u,rfl⟩ | ⟨u,rfl⟩ <;>
    rcases mixed56_cover y with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · exact (hl u v).trans (mixed56_encoded_left s t u v).symm
  · exact iff_of_false (fun h => mixed56_cross_different u v (hcp h))
      (mixed56_encoded_cross s t u v)
  · exact iff_of_false (fun h => mixed56_cross_different v u (hcp (c.symm h)))
      (fun h => mixed56_encoded_cross s t v u h.symm)
  · exact (hr u v).trans (mixed56_encoded_right s t u v).symm

def mixed56Generators : List (ColorPattern 11) :=
  [mixed56Encoded 2 4,mixed56Encoded 2 6,mixed56Encoded 1 0]

theorem mixed56_generators_complete (c : ColorPattern 11) :
    CertificateConstraint c ∧ c ≤ mixed56Pattern ↔ c ∈ mixed56Generators := by
  constructor
  · rintro ⟨hc,hcp⟩
    obtain ⟨s,t,rfl⟩ := mixed56_certificate_encoded c hc hcp
    have hnc : Mixed56Compatible s t := hc.2
    rcases (mixed56_compatible_iff s t).mp hnc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [mixed56Generators]
  · intro h
    simp only [mixed56Generators,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl | rfl | rfl <;>
      apply mixed56_encoded_certificate <;> rw [mixed56_compatible_iff] <;> decide

#print axioms mixed56_generators_complete
end LC004

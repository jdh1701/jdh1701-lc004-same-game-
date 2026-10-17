import LC004.CertifiedPaths

namespace LC004

/-- Heavy-bit upgrades simulate each step at the very same run index. -/
theorem stepAt_heavier {s t u : RunState} {i : Nat}
    (hh : Heavier s t) (hs : stepAt s i = some u) :
    ∃ v, stepAt t i = some v ∧ Heavier u v := by
  induction s generalizing t u i with
  | nil => simp [stepAt] at hs
  | cons x xs ih =>
      rcases x with ⟨c,b⟩
      obtain ⟨e,ys,rfl,hb,ht⟩ := heavier_head_shape hh
      cases i with
      | zero =>
          cases b with
          | false => simp [stepAt] at hs
          | true =>
              have he : e = true := hb rfl
              subst e
              simp only [stepAt, ↓reduceIte, Option.some.injEq] at hs
              subst u
              exact ⟨ys, rfl, ht⟩
      | succ i =>
          cases xs with
          | nil => simp [stepAt] at hs
          | cons y post =>
              rcases y with ⟨d,f⟩
              obtain ⟨g,post',rfl,hf,hpost⟩ := heavier_head_shape ht
              cases i with
              | zero =>
                  cases f with
                  | false => simp [stepAt] at hs
                  | true =>
                      have hg : g = true := hf rfl
                      subst g
                      cases post with
                      | nil =>
                          have hp : post' = [] := by
                            cases post' <;> simp_all [Heavier]
                          subst post'
                          simp only [stepAt, ↓reduceIte, Option.some.injEq] at hs
                          subst u
                          exact ⟨[(c,e)], rfl, ⟨rfl, hb, trivial⟩⟩
                      | cons z zs =>
                          rcases z with ⟨a,h⟩
                          obtain ⟨k,zs',rfl,hk,hzs⟩ := heavier_head_shape hpost
                          by_cases hca : c = a
                          · simp [stepAt, hca] at hs
                            subst u
                            exact ⟨(c,true)::zs', by simp [stepAt, hca],
                              ⟨hca.symm, (fun h => h), hzs⟩⟩
                          · simp [stepAt, hca] at hs
                            subst u
                            exact ⟨(c,e)::(a,k)::zs', by simp [stepAt, hca],
                              ⟨rfl, hb, rfl, hk, hzs⟩⟩
              | succ j =>
                  cases hstep : stepAt ((d,f)::post) (j+1) with
                  | none => simp [stepAt, hstep] at hs
                  | some u' =>
                      obtain ⟨v,hv,huv⟩ := ih ht hstep
                      simp [stepAt, hstep] at hs
                      subst u
                      exact ⟨(c,e)::v, by simp [stepAt, hv],
                        ⟨rfl, hb, huv⟩⟩

/-- Every successful index sequence survives any heavy-bit upgrades. -/
theorem successfulPath_heavier {s t : RunState} {p : List Nat}
    (hh : Heavier s t) (hp : SuccessfulPath s p) : SuccessfulPath t p := by
  induction p generalizing s t with
  | nil =>
      have he := successfulPath_nil_iff.mp hp
      subst s
      have ht : t = [] := by cases t <;> simp_all [Heavier]
      exact successfulPath_nil_iff.mpr ht
  | cons i rest ih =>
      cases hs : stepAt s i with
      | none => simp [SuccessfulPath, follow, hs] at hp
      | some u =>
          obtain ⟨v,hv,huv⟩ := stepAt_heavier hh hs
          have hrest : SuccessfulPath u rest := by
            simpa [SuccessfulPath, follow, hs] using hp
          simpa [SuccessfulPath, follow, hv] using ih huv hrest

theorem solutionPaths_mono {s t : RunState} (hh : Heavier s t) :
    solutionPaths s ⊆ solutionPaths t := by
  intro p hp
  exact (mem_solutionPaths_iff _ _).mpr
    (successfulPath_heavier hh ((mem_solutionPaths_iff _ _).mp hp))

theorem solutionPaths_card_mono {s t : RunState} (hh : Heavier s t) :
    (solutionPaths s).card ≤ (solutionPaths t).card :=
  Finset.card_le_card (solutionPaths_mono hh)

/-- Ambiguity is upward closed. This supports minimal-obstruction searches
without imposing any finite bound on the size of an obstruction. -/
theorem ambiguity_heavier {s t : RunState} (hh : Heavier s t)
    (ha : 2 ≤ (solutionPaths s).card) :
    2 ≤ (solutionPaths t).card :=
  ha.trans (solutionPaths_card_mono hh)

/-- Removing optional heavy bits preserves uniqueness whenever a successful
path remains. On our palindromic candidates the median path supplies it. -/
theorem uniqueSuccessfulPath_of_heavier {s t : RunState} {p : List Nat}
    (hh : Heavier s t) (hu : UniqueSuccessfulPath t)
    (hp : SuccessfulPath s p) : UniqueSuccessfulPath s := by
  obtain ⟨q,hq,huniq⟩ := hu
  refine ⟨p,hp,?_⟩
  intro r hr
  exact (huniq r (successfulPath_heavier hh hr)).trans
    (huniq p (successfulPath_heavier hh hp)).symm

end LC004

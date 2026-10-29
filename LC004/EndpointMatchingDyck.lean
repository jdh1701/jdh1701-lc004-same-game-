import LC004.EndpointMatching

namespace LC004.EndpointMatching

noncomputable def toDyck {n : Nat} (m : EndpointMatching n) : DyckWord :=
  matchingToDyckWord m.pattern m.pattern_noncrossing

theorem step_formula {n : Nat} (m : EndpointMatching n) (i : Fin n) :
    matchingDyckStep m.pattern m.pattern_noncrossing i =
      if i < m.mate i then DyckStep.U else DyckStep.D := by
  classical
  simp only [matchingDyckStep, pattern_partner]

theorem toDyck_append {n k : Nat} (m : EndpointMatching n) (t : EndpointMatching k) :
    (m.append t).toDyck = m.toDyck + t.toDyck := by
  classical
  have hleft (i : Fin n) :
      matchingDyckStep (m.append t).pattern (m.append t).pattern_noncrossing (Fin.castAdd k i) =
        matchingDyckStep m.pattern m.pattern_noncrossing i := by
    rw [step_formula, step_formula]
    simp only [append, appendMate, Fin.addCases_left, Fin.lt_def, Fin.coe_castAdd]
  have hright (i : Fin k) :
      matchingDyckStep (m.append t).pattern (m.append t).pattern_noncrossing (Fin.natAdd n i) =
        matchingDyckStep t.pattern t.pattern_noncrossing i := by
    rw [step_formula, step_formula]
    simp only [append, appendMate, Fin.addCases_right, Fin.lt_def, Fin.coe_natAdd,
      Nat.add_lt_add_iff_left]
  apply DyckWord.ext
  change List.ofFn (matchingDyckStep (m.append t).pattern (m.append t).pattern_noncrossing) =
    List.ofFn (matchingDyckStep m.pattern m.pattern_noncrossing) ++
      List.ofFn (matchingDyckStep t.pattern t.pattern_noncrossing)
  rw [List.ofFn_add]
  exact congrArg₂ List.append (congrArg List.ofFn (funext hleft))
    (congrArg List.ofFn (funext hright))

theorem toDyck_nest {n : Nat} (m : EndpointMatching n) : m.nest.toDyck = m.toDyck.nest := by
  classical
  let f := matchingDyckStep m.nest.pattern m.nest.pattern_noncrossing
  let g := matchingDyckStep m.pattern m.pattern_noncrossing
  have hzero : f 0 = DyckStep.U := by
    dsimp [f]
    rw [step_formula]
    simp [nest, nestMate_zero, Fin.lt_def]
  have hlast : f (Fin.last (n + 1)) = DyckStep.D := by
    dsimp [f]
    rw [step_formula]
    simp [nest, nestMate_last, Fin.lt_def]
  have hinterior (i : Fin n) : f (interior i) = g i := by
    dsimp [f, g]
    rw [step_formula, step_formula]
    change (if interior i < nestMate m (interior i) then DyckStep.U else DyckStep.D) =
      (if i < m.mate i then DyckStep.U else DyckStep.D)
    rw [nestMate_interior]
    simp only [interior, Fin.lt_def, Fin.val_succ, Fin.coe_castSucc, Nat.add_lt_add_iff_right]
  apply DyckWord.ext
  change List.ofFn f = [DyckStep.U] ++ List.ofFn g ++ [DyckStep.D]
  rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append]
  have hinner : List.ofFn (fun i : Fin n => f (interior i)) = List.ofFn g :=
    congrArg List.ofFn (funext hinterior)
  change f 0 :: (List.ofFn (fun i : Fin n => f (interior i)) ++
    [f (Fin.last (n + 1))]) = [DyckStep.U] ++ List.ofFn g ++ [DyckStep.D]
  rw [hzero, hlast, hinner]
  rfl

def empty : EndpointMatching 0 where
  mate i := Fin.elim0 i
  twice i := Fin.elim0 i
  nofixed i := Fin.elim0 i
  noCross a := Fin.elim0 a

theorem toDyck_empty : empty.toDyck = 0 := by
  apply DyckWord.ext
  rfl

#print axioms toDyck_append
#print axioms toDyck_nest

end LC004.EndpointMatching

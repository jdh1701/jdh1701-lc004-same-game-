"""Generate untrusted shape witnesses; Lean checks every witness against geometry.
No native evaluation, generated axioms or imported computational receipts are used.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ROWS = json.loads((ROOT / 'research/five_geometry_20261029/ten_split_check.json').read_text())['rows']


def write_generated(path, text):
    if "--check" in sys.argv:
        assert path.read_text() == text, f"Stale generated Lean source: {path}"
    else:
        path.write_text(text)


def natlist(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def predicate(rows):
    e = set(map(tuple, rows['compatible_pairs']))
    us = sorted({x for x, _ in e})
    vs = sorted({y for _, y in e})
    u = f'(fun x : Fin 10 => x.val ∈ ({natlist(us)} : List Nat))'
    v = f'(fun y : Fin 10 => y.val ∈ ({natlist(vs)} : List Nat))'
    if not e:
        return 'False', 'choiceRelationClosed_empty', 'empty'
    rect = f'(x.val ∈ ({natlist(us)} : List Nat) ∧ y.val ∈ ({natlist(vs)} : List Nat))'
    if e == {(x, y) for x in us for y in vs}:
        return rect, f'choiceRelationClosed_rectangle {u} {v}', 'rectangle'
    if len(e) == 2:
        (a,b),(c,d) = sorted(e)
        return f'((x = {a} ∧ y = {b}) ∨ (x = {c} ∧ y = {d}))', f'choiceRelationClosed_twoPoints ({a} : Fin 10) {c} ({b} : Fin 10) {d}', 'two_points'
    for p in us:
        for q in vs:
            if e == {(x,y) for x in us for y in vs if x == p or y == q}:
                expr = f'({rect} ∧ (x = {p} ∨ y = {q}))'
                closed = f'choiceRelationClosed_inter (choiceRelationClosed_rectangle {u} {v}) (choiceRelationClosed_fan ({p} : Fin 10) ({q} : Fin 10))'
                return expr, closed, 'fan'
    raise ValueError(rows)


shapes = {}
for shard in range(6):
    body = [f'import LC004.FiveClassGeometryCases{shard-1}\n\nset_option Elab.async false\n\nnamespace LC004\n' if shard else 'import LC004.FiveClassFiniteGeometry\n\nset_option Elab.async false\n\nnamespace LC004\n']
    these = ROWS[42*shard:42*(shard+1)]
    for k, r in enumerate(these, 42*shard):
        g = natlist(r['left'])
        spec, closed, shape = predicate(r)
        shapes[shape] = shapes.get(shape, 0) + 1
        body += [f'\n/-- Exhaustive finite relation {k}; shape: {shape}. -/\n',
                 f'theorem fiveGeometrySpec{k:03} : ∀ x y : Fin 10,\n',
                 f'    FiveCompatible {g} (fiveOtherRanks {g}) x y ↔ {spec} := by\n  apply finiteRelationMatches_sound\n  decide +kernel\n',
                 f'\ntheorem fiveGeometryCase{k:03} : FiveGeometryCase {g} := by\n',
                 f'  refine ⟨(choiceRelationClosed_congr fiveGeometrySpec{k:03}).mpr ?_, ?_⟩\n',
                 f'  · exact {closed}\n']
        if r['crossing']:
            p,q = r['cover']
            body += [f'  · intro _\n    refine ⟨{p}, {q}, ?_⟩\n',
                     f'    have h : ∀ x y : Fin 10, {spec} → x = {p} ∨ y = {q} := by decide +kernel\n',
                     f'    intro x y hxy\n    exact h x y ((fiveGeometrySpec{k:03} x y).mp hxy)\n']
        else:
            body += [f'  · intro hc\n    have hn : finiteBlockCross {g} (fiveOtherRanks {g}) = false := by decide +kernel\n',
                     f'    have ht := (finiteBlockCross_iff {g} (fiveOtherRanks {g})).mpr hc\n',
                     '    rw [hn] at ht\n    contradiction\n']
    glist = '[' + ',\n  '.join(natlist(r['left']) for r in these) + ']'
    body += [f'\ndef fiveGeometryChunk{shard} : List (List Nat) :=\n  {glist}\n',
             f'\ntheorem fiveGeometryChunk{shard}_checked : ∀ g ∈ fiveGeometryChunk{shard}, FiveGeometryCase g := by\n',
             '  intro g hg\n',
             f'  simp only [fiveGeometryChunk{shard}, List.mem_cons, List.mem_nil_iff, or_false] at hg\n',
             '  rcases hg with ' + ' | '.join(f'h{k}' for k in range(42)) + '\n']
    for k in range(42):
        body += [f'  · subst g\n    exact fiveGeometryCase{42*shard+k:03}\n']
    body += ['\nend LC004\n']
    write_generated(ROOT / f'LC004/FiveClassGeometryCases{shard}.lean', ''.join(body))

body = [f'import LC004.FiveClassGeometryCases{k}\n' for k in range(6)]
body += ['\nnamespace LC004\n\ndef fiveInterleavingInventory : List (List Nat) :=\n  ',
         ' ++ '.join(f'fiveGeometryChunk{k}' for k in range(6)), '\n',
         '\ntheorem fiveInterleavingInventory_count : fiveInterleavingInventory.length = 252 := by decide +kernel\n',
         '\n/-- Every sorted five-element subset of the ten ranks appears in the checked inventory. -/\n',
         'theorem fiveInterleavingInventory_complete :\n',
         '    ((List.range 10).sublistsLen 5).all (fun g => fiveInterleavingInventory.contains g) = true := by\n  decide +kernel\n',
         '\n/-- Kernel-checked local geometry for every five-versus-five rank interleaving. -/\n',
         'theorem fiveClass_finite_geometry (g : List Nat)\n',
         '    (hg : g ∈ (List.range 10).sublistsLen 5) : FiveGeometryCase g := by\n',
         '  have hm := (List.all_eq_true.mp fiveInterleavingInventory_complete) g hg\n',
         '  have hi : g ∈ fiveInterleavingInventory := List.contains_iff_mem.mp hm\n',
         '  simp only [fiveInterleavingInventory, List.mem_append, or_assoc] at hi\n',
         '  rcases hi with h | h | h | h | h | h\n']
body += [f'  · exact fiveGeometryChunk{k}_checked g h\n' for k in range(6)]
body += ['\n#print axioms fiveClass_finite_geometry\nend LC004\n']
write_generated(ROOT / 'LC004/FiveClassGeometryExhaustive.lean', ''.join(body))
print(json.dumps(dict(rows=len(ROWS),shards=6,shapes=shapes)))

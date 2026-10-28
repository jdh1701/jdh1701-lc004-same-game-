# Same Game research: contextual insertion of arbitrary winning words
Date: 2026-10-28

## Novel research conjecture, NOT proved
Let W denote the language of strings that can be cleared by legal maximal-run deletions. For any words x,y,v over the same finite alphabet:

  (x ++ y in W) AND (v in W) ==> (x ++ v ++ y in W).

This extends the tested monochromatic block insertion conjecture to *arbitrary winning words*.

## Independent finite falsification (executed Python locally)
q=2, original lengths 0..8: 233 winning words, 442001 placements checked, no counterexample.
q=3, original lengths 0..7: 457 winning words, 1556542 placements checked, no counterexample.
q=4, original lengths 0..6: 369 winning words, 896301 placements checked, no counterexample.
TOTAL: 2,894,844 checks, zero failures.

For every pair of winning words from the indicated finite set, every insertion gap in the outer word was tested against a recursive maximal-run solver. The inserted strings can be longer than the bound on the original inputs.

## New Lean factoring (source submitted; no kernel check obtained)
LC004/ConditionalInsertion.lean introduces three conditional results:
1. win_of_erases_of_lift: lift backward closure through any sequence of auxiliary adjacent pair/triple deletions.
2. win_insert_erasable_of_lift: inserting ANY word with an Erases middle [] certificate preserves the target Win predicate in any context.
3. win_insert_grammar_of_lift: same with Grammar q middle, using the previously proposed grammar_erases_empty proof.

No axiom is introduced: the critical lifting property remains an explicit parameter
  lift : ∀ {u v}, SmallErase u v → Win v → Win u.

Therefore the Lean source does NOT prove insertion closure for the original maximal-run game without discharging lift AND proving that every original-game-winning word admits an Erases certificate. The latter can be approached by splitting maximal runs of length >=2 into 2/3 blocks.

## Higher-value mathematical structure
If the conjecture is true, the winning language is closed under contextual insertion of its own words. This is stronger than a submonoid under concatenation and indicates a possible insertion grammar. It does NOT by itself solve distinct-word enumeration or eliminate multiple derivations.

## Verification limitations
The local environment has no lean/lake and cannot resolve github.com for a clone. GitHub connector accepts source commits but the accessible status and workflow-run queries do not furnish a successful build. New Lean theorems remain SUBMITTED, NOT VERIFIED.

Repo: https://github.com/jdh1701/jdh1701-lc004-same-game-

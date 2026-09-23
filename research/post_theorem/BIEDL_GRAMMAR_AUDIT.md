# Biedl grammar ambiguity versus deletion-path ambiguity

Source: T. C. Biedl, E. D. Demaine, M. L. Demaine, R. Fleischer, L. Jacobsen,
and J. I. Munro, *The Complexity of Clickomania*, arXiv:cs/0107031v1,
section 2.2, PDF pp. 2–4: https://arxiv.org/pdf/cs/0107031.

## Exact printed CFG

For each color `c`, the paper gives

```
S -> epsilon | SS | c S c | c S c S c
```

Theorem 2 proves that the **language** of this grammar equals the solvable
one-row/one-column Clickomania words. The paper's theorem does not claim a
correspondence between parse trees and solutions. Its conclusion (PDF pp.
13–14, open problem 3) asks whether an LR(k) grammar can be constructed.

## Counting convention and unavoidable pathology

The printed CFG has infinitely many derivation trees for every accepted word,
including the empty word: from any derivation, replace an occurrence of `S`
by `S -> SS`, with the left child `S -> epsilon`, and retain the original
derivation in the right child. Repeat arbitrarily often. Thus literal `G(w)`
is infinite for every winning word. The following finite comparison uses a
**modified counting convention**, not the literal CFG parse count: both
children of every `S -> SS` must derive nonempty strings. Nullable children
remain allowed in the other two productions. This removes the infinite
epsilon-padding without changing the generated language.

`P(w)` counts ordered legal maximal-run deletion sequences to the empty word.
Deletion of different run indices at a state produces different paths,
including when the resulting ordinary words coincide.

## Earliest substantive discrepancy, with two opposite directions

| Word | P(w) | Epsilon-pruned G(w) | Explanation |
|---|---:|---:|---|
| `aaaa` | 1 | 2 | One deletion; parses by `a S a` wrapping `aa` and by `SS` splitting `aa|aa`. |
| `aabb` | 2 | 1 | Either maximal run can be removed first; the only pruned parse is `SS` splitting `aa|bb`. |

Exhaustive lexicographic enumeration over two colors through length 10 and
three colors through length 8 found no language-membership discrepancy.
For both alphabet sizes, length 4 is the first length at which
`P(w)=1 iff G(w)=1` fails. This is a finite check, while the two explicit
words themselves rigorously refute the proposed equivalence for the stated
pruning convention.

At length 4 the distributions among winning ordinary words are:

| q | P=1,G=1 | P=1,G>1 | P>1,G=1 | P>1,G>1 |
|---:|---:|---:|---:|---:|
| 2 | 2 | 2 | 2 | 0 |
| 3 | 6 | 3 | 6 | 0 |

`aaaa` illustrates ambiguity between concatenation and nested wrapping;
`aabb` illustrates path-order ambiguity absent in the parse. A different
normalization of grammar parse trees could yield different finite values,
so claims about `G(w)` must specify that normalization exactly.

## Reproduction

```
python biedl_grammar_audit.py > biedl_grammar_audit_output.txt
```

No randomness or external data. Python's standard library only. The file
`biedl_grammar_audit_output.txt` records every length's four-category count
and lexicographically earliest examples. These are ordinary labeled words,
not color-relabeling or reversal classes.

## Implication

The LC004 unique-successful-path theorem does not directly remove the
ambiguity of Biedl's printed CFG. A grammar-based counting method would need
its own canonical parse or an explicit multiplicity correction. This does
not rule out another use of the theorem in enumeration.

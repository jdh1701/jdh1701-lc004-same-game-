# Binary unique-path counting: candidate theorem and complete paper argument

Status: a mathematical proof argument is supplied below, with exhaustive
and held-out checks. **The classification and generating function have not
been checked by Lean.** They must not be confused with the kernel-checked
median and colour-palindrome results. Bibliographic priority is unresolved.

## Definitions and proposed classification

Use maximal runs, threshold two, and indexed deletion sequences. A normalized
binary state alternates colours. A heavy run has at least two cells; a light
run has one. Empty input has one empty successful path.

For a nonempty state with `2m+1` runs, index runs `0,...,2m`.
For `m>=1`, the proposed necessary and sufficient conditions for exactly one
successful complete path are:

1. Run `m` is heavy.
2. The two endpoint runs `0` and `2m` are not both heavy.
3. At least one of the two **interior** sides `1,...,m-1` and
   `m+1,...,2m-1` consists entirely of light runs.

A one-run state is unique precisely when heavy. Even run counts are excluded
by the median necessity theorem, not by an arbitrary counting convention.

## Prior lemmas used

Biedl et al., *The Complexity of Clickomania*, §2.3,
https://arxiv.org/pdf/cs/0107031 :

* Lemma 8: in a solvable binary state with N runs, a consecutive light block
  of length L satisfies `2L<=N-1` at an endpoint and `2L<=N-2` internally.
* Lemma 9: an odd-run binary state with heavy median is solvable by successive
  median deletion.
* Theorem 12: an even-run binary state is solvable iff some odd-indexed cut
  (in the paper's one-based indexing) splits it into two solvable odd-run
  states. Equivalently the left part has an odd number of runs.

The all-colour median **necessity under uniqueness** is the separate theorem
formalized in `LC004/UniqueMedian.lean`; the binary median solving construction
itself is prior work.

## Necessity argument

The median necessity theorem supplies an odd run count and a heavy median.
If both endpoints are heavy, delete the left endpoint and then the right
endpoint. The remaining odd-run binary state still has the original heavy
median. Lemma 9 solves it. This gives a successful first move different from
the median, contradicting uniqueness.

Suppose instead there is an interior heavy run i<m and an interior heavy run
j>m. Delete i first. This is a bridge move. The number of runs becomes
`2m-1`; the original heavy median (possibly absorbed in the merge) is at index
`m-2`. The selected right-side heavy run survives at index `j-2`, which is
at least `m-1` and is not an endpoint. If `j-2=m-1`, it is the new median,
and Lemma 9 applies. Otherwise delete that right-side run as a second move.
The number of runs is now `2m-3`, whose median index is `m-2`; the original
heavy median remains there, so Lemma 9 again applies. In either case the
first deletion was not the median, contradicting uniqueness. This proves
condition 3. The case m=1 has no interior side and needs no such argument.

## Sufficiency argument

By reversal symmetry assume the right interior side is all light. The median
chain always solves the state. We show that every other legal first deletion
is unsuccessful, then apply the existing uniqueness equivalence.

* **Left endpoint deleted.** It must be heavy, so condition 2 makes the right
  endpoint light. After deletion N=`2m`; the m rightmost runs are light.
  This violates the endpoint bound `2L<=N-1`.
* **An interior left run deleted.** The binary bridge leaves N=`2m-1`.
  The right interior light block retains length `m-1`. If the right endpoint
  is heavy, this block is internal, violating `2L<=N-2`. If the right endpoint
  is light, it extends to an endpoint block of length at least m, violating
  `2L<=N-1`. This case only arises when m>=2.
* **Right endpoint deleted.** It is heavy, so the left endpoint is light.
  The child has `2m` runs and a light suffix of length at least `m-1`.
  In any split from Theorem 12, a nonempty right part cut entirely within
  that suffix is all light and unsolvable. Every other right part contains
  the full suffix, so the endpoint bound requires its run count to be at
  least `2m-1`. The left part therefore has at most one run. It must have one
  run, which is the original light left endpoint and is unsolvable. For m=1
  the only possible odd split likewise has a singleton left part.

There are no heavy right-interior runs. Thus the median is the sole
successful first move. The existing uniqueness theorem gives a unique
complete successful path. The proof uses maximal runs throughout; deleting
an endpoint cannot merge across a wraparound boundary.

## Weighted count derived from the classification

Let t mark heavy **noncentral** runs. The endpoint pair contributes
`1+2t`. The interior side choices contribute
`2(1+t)^(m-1)-1`, subtracting the case with both interiors entirely light
that would otherwise be counted twice. Hence, for m>=1,

`F_m(t) = (1+2t)(2(1+t)^(m-1)-1)`; `F_0(t)=1`.

At t=1 this gives `3(2^m-1)` normalized unique flag patterns for m>=1.
There are two labelled alternating colour patterns. Raw expansions require
weight L(z)=z for light runs and H(z)=z²/(1-z) for heavy runs. Therefore the
nonempty binary unique-word generating function predicted by the theorem is

`U_2(z) = 2 H(z) [1 + 2z²(1+z)/(1-z-z²) - z²/(1-z)²]`.

Equivalently,

`U_2(z) = 2z²(1-3z+3z²-2z⁴+2z⁵) / ((1-z)³(1-z-z²))`.

Include the empty word by adding 1. For n>=8 the proposed coefficient
recurrence is

`u_n = 4u_(n-1)-5u_(n-2)+u_(n-3)+2u_(n-4)-u_(n-5)`.

Initial `u_0,...,u_7` are `1,0,2,2,4,8,14,26`. The empty term changes no
coefficient from n=1 onward. These counts enumerate words, not paths,
cyclic necklaces, unlabelled colours, or grammar derivations.

## Discriminating execution

`binary_unique_conjecture.py` checks the classifier against the exact
deletion solver on all flag assignments with heavy median through 21 runs
(m=0,...,10). The m=8,9,10 cases were held out after fitting the formula
through m=7. It additionally checks all binary raw words at lengths 15–18
and obtains 2278, 3760, 6172, 10090 unique words. These agree with the weighted
formula. The exact domains, elapsed runtime and literal output are saved in
`data/binary_unique_conjecture.json` and `logs/binary_unique_conjecture.log`.

The program retains its original name and conservative CONJECTURE status:
finite computation alone does not certify the universal paper argument.
The next formal target is to encode the cited checkerboard and even-split
lemmas, then discharge the classification against `IndexedStep`.

## Separate multicolour subclass

For palindromic run-colour skeletons with all `m+1` colours on one half
(including the centre) distinct, a heavy centre and no heavy-heavy mirror
pair are necessary and sufficient for uniqueness. Each shell colour has
only its two mirror runs. Deleting an off-centre heavy run whose mirror is
light leaves that colour globally singleton and therefore impossible to
remove. Deleting a heavy-heavy mirror pair first, one after the other,
leaves a solvable median chain, proving necessity. Thus this subclass has
exact weighted series

`D_q(z) = H(z) * sum_(m=0)^(q-1) (q)_(m+1) * (z²+2zH(z))^m`.

Here `(q)_k` is the falling factorial. Parameters reconstruct a unique raw
word, so there is no tree/grammar multiplicity. The formula passed the raw
word cross-checks and 21,845 separate flag assignments through 15 runs.
It is not a formula for all unique multicolour words or for all winning words.

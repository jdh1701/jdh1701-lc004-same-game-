# Corrections to the Lean research journal

## Attribution and scope

The grammar characterization is published prior work: Therese C. Biedl,
Erik D. Demaine, Martin L. Demaine, Rudolf Fleischer, Lars Jacobsen, and
J. Ian Munro, *The Complexity of Clickomania*, in *More Games of No Chance*,
MSRI Publications 42 (2002), pp. 389–404, Theorem 2; preprint arXiv:cs/0107031.
The pair/triple certificate characterization mechanizes that established
structural content. It is not presented as a new solvability characterization.
https://library.slmath.org/books/Book42/files/biedl.pdf

The refined counts D and T are specializations of Kreweras's 1972 formula
for noncrossing partitions of prescribed block sizes. With m_j blocks of
size j, n positions and b blocks, the count is
n! / ((n+1-b)! * product_j(m_j!)). Substituting m_4=1, m_2=k-1 gives
D=choose(2k+2,k-1); substituting m_3=2, m_2=k-2 gives
2T=(k-1)*choose(2k+2,k-1), for k>=2. These are known mathematical truths;
the remaining obligations concern their formalization in our finite model.

A direct bijective treatment is S. C. Liaw, H. G. Yeh, F. K. Hwang, and
G. J. Chang, *A simple and direct derivation for the number of noncrossing
partitions*, Proceedings of the AMS 126(6) (1998), 1579–1581,
DOI 10.1090/S0002-9939-98-04546-8, Theorem 1.
The degree-word and cyclic-root route belongs to the classical
Lukasiewicz-word/cycle-lemma framework. No novelty is claimed for it.

The prospective counting contribution is the application to winning color
patterns A(n,k), especially A(2k+2,k). Its novelty is not established.
OEIS A323844 already records the named-alphabet winning-count array and
Kurz's fixed-length polynomials. These must be compared after conversion
to the falling-factorial basis, not mistaken for an unrelated sequence.
An unsuccessful web search for flattened coefficients is not an exhaustive
OEIS lookup and supplies no priority evidence.
https://oeis.org/A323844

## Build coverage correction

At a734a54, the tree contained 131 modules, 436 explicit theorem/lemma
declarations and 10335 lines. Five modules (7 theorems, 275 lines) were
outside the root import closure, so the successful build covered 126 active
modules with 429 such declarations and 10060 lines. The terminal theorems
did not depend on the five excluded modules. The old journal conflated
source inventory with compiler coverage. That claim is retracted.

The five abandoned files are removed from LC004 and preserved as historical
.lean.txt files under research/archive/unverified_boundary_attempts.
No compilation claim is made for these archive files. In particular, the
unrestricted prefix-stripping assertion is false: deleting the middle run
of [(0,false),(1,true),(0,false)] merges its outer runs, whereas stripping
the prefix first and reattaching it leaves two separate runs. A new active
Lean regression theorem records this obstruction.

## Reproducibility and range

The project now commits a pinned lake-manifest.json, checks the complete
active import closure, and includes a compiler-level axiom allowlist audit
of every declaration owned by a project module, including private and
generated declarations. CI must fail on sorryAx or any dependency outside
propext, Classical.choice and Quot.sound. The manifest is checked for
unexpected mutation after restoring dependencies and building.

The conditional terminal theorem now requires k>=1, since all its arithmetic
lemmas already support that range. At k=1 the mathematical count is A(4,1)=1,
D=1 and T=0. Extending the conditional theorem does not by itself formalize
those separate endpoint cardinalities. The factorial expression involving
(k-2)! is reserved for k>=2.

## Comparison of formalization routes

Both routes prove established counts. The existing word route already has
canonical class minima, prefix balance and positive-arity preservation.
It still needs the universal noncrossing inverse and a cyclic-root theorem.

A marked special-block route instead rotates actual NC partitions, cuts at
the special block, and counts the resulting Catalan gaps. Mathlib v4.19.0
contains the binary Catalan recurrence (catalan_succ / catalan_succ'), but a
source search found no general cycle-lemma or the required higher convolution
evaluation in the relevant combinatorics/list directories. This search is
an implementation assessment, not a theorem of nonexistence.

For D, if m=k-1 and F_4(m) counts four Catalan gap pieces with total
semilength m, the pointed identity is 4D=(2k+2)*F_4(k-1).
For T, marking one triple and requiring it to contain position zero gives
6T=(2k+2)*H_3(k-2), where H_3 counts three gaps with one triple among them
and pairs elsewhere. This route therefore needs NC rotation/gap equivalences
and a one-triple class as well as convolution identities. It is not yet
shown cheaper than reusing the already formalized degree-word foundation.
No universal inverse, rotation theorem, refined count, or route-optimality
claim is asserted here.

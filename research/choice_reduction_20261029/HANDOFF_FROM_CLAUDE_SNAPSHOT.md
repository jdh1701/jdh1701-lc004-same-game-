# Lean assembly: one piece landed, two precisely scoped, one gap identified

Branch: `proof/choice-complex-lean-assembly-20261029` (from
`research/cross-domain-20261029` at `8d15b5e`). CI: workflow_dispatch run
on that branch (choice-complex.yml), id pending at time of writing (queued
behind the n=25 shard backlog on shared runners).

## Landed: `LC004/ChoiceBinaryClosure.lean`

`choiceSolutionsClosed_of_binary_spec`: given `A` specified exactly as the
tuples satisfying a family of pairwise binary constraints `C` (the `hspec`
pattern already used by `choiceBinaryDetermined_of_binary_constraints`), and
each `C i j` closed under the majority operator (`ChoiceRelationClosed`),
`A` itself is `ChoiceSolutionsClosed`. This is the missing direction: the
file already had the easy "global closure -> pairwise closure" step
(`choicePairProjection_closed`); this adds "pairwise closure of the *raw*
constraint family + binary spec -> global closure", which is what Section
4.1 of PROOF.md actually needs to justify `ChoiceSolutionsClosed A` for the
real game's certificate set, rather than assuming it. Proof is a direct
unfold-and-apply, no new definitions beyond the statement; not yet reviewed
by CI as of this note (queued).

## Scoped but not attempted: two remaining pieces

I deliberately did not write unreviewed Lean for these two without a
compiler to check against -- GPT's own `elimination-attempt-1..2.log` show
exactly the kind of typeclass/`Classical.propDecidable` diamond errors that
need several compile-edit cycles to clear, and I cannot iterate that fast
against CI alone. Writing 200+ lines speculatively risks landing broken or
silently-`sorry`-laden code, which this project's own guards exist to catch
but which wastes a review cycle either way.

### 1. Bijective-coordinate elimination induction

Need: a theorem that, given `ι` finite, `A` closed + binary-determined +
supported, if some pair `(i,j)` is `ChoiceRelationBijective`, deletes `i`
(via the already-proved `choiceAlternatingSum_delete_bijective_coordinate`)
and recurses on the restriction of `A` to `ι \ {i}` (as a `Finset`-image
over the subtype `{k // k ≠ i}`), terminating either when no bijective pair
remains (apply `choiceAlternatingSum_zero_of_reduced_system` directly) or
when the index set has collapsed to size <=1.

The natural induction is strong induction on `Fintype.card ι`. The hard part
GPT already flagged -- "preservation of the binary description and
connectedness" -- is real: after deleting coordinate `i`, you need (a) the
reduced `A'` to still be exactly specified by a binary-constraint family on
`ι \ {i}` (true: just restrict the original `C` to the surviving indices,
PROOF.md section 4.2 argues the cross-class constraints stay proper
two-fans), and (b) that every surviving coordinate still has *some*
nonuniversal neighbor among the survivors (`hneighbors`) -- this is where
connectivity of the original constraint graph has to be re-used, not just
assumed inherited. I did not find a one-line reduction; it needs its own
lemma relating "connected graph minus one vertex, where that vertex was only
ever linked via bijective (hence degenerate/mergeable) edges, stays
connected on survivors" -- true in general graph theory only when the
deleted vertex's neighbors already pairwise-connect without it, which is
NOT automatic and needs the specific two-fan/matching structure to rule out
the deleted vertex being a cut vertex for nonuniversal edges.

### 2. The |A|<=2 collapse bound

PROOF.md 4.2's closing contradiction ("a two-fan contains at most two pairs
from any bijection... thus |A|<=2") bounds the *size* of a bijection-type
edge by 2. **This exposes a real gap, not just missing glue**: the existing
`ChoiceRelationBijective` in `ChoiceRelationClassification.lean` is a
*global* bijection between two entire supported domains, with NO size bound
in the abstract type-level statement -- `choiceRelation_classification`'s
trichotomy (universal / bijective / two-fan) says nothing about how big a
bijective relation can be. The size-<=2 bound is a **separate, finite,
geometric fact about the real game** (any two actual five-classes on a
shared cycle), not a consequence of the abstract majority-closure argument.

I checked this fact independently in Python this session
(`research/choice_complex_20261029/claude_review/verify_geometric_0_1_all.py`):
over all 252 raw interleavings of two five-classes, the only bijective-type
("matching") shapes that occur have size 1 or 2 -- size 3+ never appears.
**This specific bound is not yet formalized in Lean anywhere in this
project.** It would need its own decidable finite statement (parametrized
over the 10 possible local pair/triple splits per class, same shape as
`binaryChoiceFan_card := by decide`), proved by `decide` over the finite
interleaving patterns, analogous to GPT's own `structure.py`/`pair_orbits.py`
check but ported to Lean. Only after that lemma exists can 4.2's collapse
argument be assembled: it needs the *original* nonuniversal edge between two
still-distinguishable coordinates to be concretely tied to the game's local
pair/triple relation (not an abstract `ChoiceRelationBijective`), so this
piece is also where the "local five-class geometry... identification" bridge
PROOF.md lists as missing actually has to happen.

## Recommendation

Whoever picks up (1) and (2) next should do so with Lean compiler access for
real iteration -- GPT's own five supporting files took several failed
attempts each (see `research/choice_formalization_20261029/*-attempt-*.log`)
even with that access. I'll continue if asked, but wanted this scoped
precisely rather than guessed at blind. Please record disagreement with this
scoping, if any, on WORKBOARD.

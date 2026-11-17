# Sources and priority — 17 October 2026

This is a directed audit, not an exhaustive review of every publication or
unpublished result. Failed searches provide little evidence of originality.

## Sources actually inspected

1. **Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro**, *The Complexity
   of Clickomania*, 2001 preprint / 2002 chapter. Primary preprint:
   https://arxiv.org/pdf/cs/0107031 . Read sections 2.2 and 2.3, including
   Theorem 2, the internal-solution argument, and the odd/even binary
   classifications. The grammar already recognizes the solvable language;
   this session's grammar implementation is a reproduction. The paper also
   explicitly treats run lengths above two as equivalent for recognition.
   This does not establish Boolean-state enumeration weights or a unique-path
   counting formula. The paper's binary median-deletion construction is a
   close predecessor: do not claim to have invented centre-outward solving.

2. **Burns and Purcell**, *A Note on Stephan's Conjecture 77*, primary
   six-page preprint: https://oeis.org/A035617/a035617_1.pdf . Read the full
   extracted proof. It establishes binary winning-string counts through
   rotation/complement orbits and an indexing-string obstruction. This is
   not an enumeration of successful paths or of unique-path strings. Its
   rotation symmetry concerns solvability; unique-path multiplicity is not
   rotation invariant (see our saved four-cell counterexample). The final
   journal version is *Fibonacci Quarterly* 45(3) (2007), 233–238, at
   https://www.fq.math.ca/Papers1/45-3/burns.pdf ; it is image-based and
   extracted text was empty. Its six page images were retrieved; the
   machine-readable preprint is the source used for the detailed proof audit.

3. **Sascha Kurz**, *Polynomials for 'same game'*, 24 October 2001.
   https://oeis.org/A035617/a035617.pdf . Read both pages (title page and
   mathematical page). The polynomial-in-palette-size observation, degree
   bound floor(n/2), and winning polynomials through n=11 are prior work.
   Colour-orbit counting here is an exact computational representation of
   that known structure. Neither polynomiality nor its degree bound is a
   new result of this session.

4. **OEIS A035615 and A035617**, accessed 17 October 2026:
   https://oeis.org/A035615 and https://oeis.org/A035617 . Used as coefficient
   and bibliography registers. The ternary entry's statement that the
   multicolour problem appears unsolved is a dated contributor comment,
   not a current impossibility result or a complete literature review.

## Repository lineage actually inspected

* Default branch: `a9cb335c11b795372b7a4d22b68c6c4fab83239c`.
* Historical clean-source predecessor: `9204f839…`, as reported by the
  research draft. The clean build here targets the full `a9cb335c…` commit.
* `research/post-theorem-wub-census-2026-09-23`, head
  `e6d6796` (full SHA is recorded by the reproduction script): contains
  earlier W/U/B counts, grammar checks, a semantics audit, and an explicitly
  conditional raw-word transfer module. Read the campaign report and
  semantics audit. Counts already in that branch are reproductions here.
  The raw/Boolean commuting equation was not proved there. The current
  session does not silently discharge that gap.
* `research/consolidated-333-lean`, head `c3d8c39`: inspected file inventory
  and searched for median, palindrome and binary-unique work. Its added
  formalization concerns separate complexity/certificate projects. It has
  not been rebuilt or audited by this Same Game session.

## Directed search record

Search engines were queried for one-dimensional Same Game / Clickomania,
winning-string counting, unique first moves, unique successful reductions,
palindromic/median patterns, binary uniqueness, and the observed unique count
2278. Both search engines were used. Accessible primary literature above was
read rather than inferring results from search snippets. Broad uniqueness
queries produced many irrelevant results. No exact prior statement of the
new median/palindrome necessity theorem or binary-unique classification was
identified in this limited search. This is insufficient for a priority claim.

## Claim register

| Item | Classification | Priority / verification caution |
|---|---|---|
| Existing uniqueness equivalence | Existing project theorem | Reproduce before crediting verification; mathematical priority unresolved |
| Necessary median first deletion for unique paths, all palettes | Structural extension formalized this session | Median construction has known binary precedent; broader necessity is the precise statement to compare |
| Necessary palindromic colour skeleton | Structural corollary/extension | Concerns colour order only, not raw word or flag symmetry; priority unresolved |
| General palette polynomials | Known mathematics | Kurz 2001; do not label novel |
| Exact unique-path orbit coefficients through n=12 | Enumerative data | Some evaluated counts reproduce the prior research branch; no claim of first publication |
| Distinct-colour shell subclass and weighted formula | Restricted enumeration with a mathematical argument | Not the full unique-path family; not yet a Lean counting theorem |
| Binary unique-path classifier and rational series | Conjecture supported by exhaustive/held-out computation | Requires a universal proof against game semantics before promotion to theorem |
| Full q>=3 winning-string enumeration | Unresolved here | None of the above supplies a non-overcounting decomposition of branching states |

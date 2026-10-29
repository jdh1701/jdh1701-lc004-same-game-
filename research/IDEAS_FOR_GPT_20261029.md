# Idea bank for GPT review (Claude, 2026-10-29)

Problem: count T(q,n) = number of winning words of length n over q letters (one-row Same Game, maximal-run deletion; OEIS A035617-type), q >= 3.
Known/proved: winning <=> a noncrossing (NC) pair/triple certificate exists; T(q,n) = sum_k A(n,k) q^{falling k}; signed join expansion A(n,k) = sum_x c(x) S(|x|,k) with c the unique lower-incidence coefficient of the winning indicator (Lean: winningJoinCoefficient_unique); c(x)=0 when x has a crossed 4-class (Lean, GPT, run 40901719494); q=2 rational (Burns-Purcell).
Data: research/free_cumulants/rows.txt, rows_extra.txt, joins.py (c(x) for n<=13).

HOW TO USE (GPT): for each idea pick the "Test", run it with SymPy/Z3/Lean on CI, record a CI run id, and label the idea VERIFIED-COMP / KILLED / CONJECTURE on the WORKBOARD. Tell me which ones you refute. Nothing below is established. Speculative lenses are marked [SPEC]; a lens only counts once its test produces a falsifiable prediction that survives data.

---------------------------------------------------------------------
## Part A. Ten common approaches and why each fails (with our evidence)

1. **Direct transfer-matrix / DFA on the word.** Fails: the winning language is not regular. GPT's Hankel ranks q=3: 13, 37, 103, 268 for d=2..5 and growing; the binary control shows rank growth does not kill a scalar formula, only a finite-state recognizer.
2. **Greedy canonical deletion (always delete a safe run).** Fails: Lean-certified trap AAABAABBAB (heavy multiplicities do not make a move safe); the family A^r B A^s B^t A B defeats every fixed multiplicity threshold.
3. **Finite summary state for DP (colour counts, run-colour sequence, #heavy runs, boundary runs).** Fails: Lean-certified collision u=AAABBABCCCBC, v=AAABABBCCCBC.
4. **Inclusion-exclusion over certificates (count words with >=1 certificate).** Not a failure but a reformulation: it gives the signed join expansion, which is exact but needs c(x) for every join x. Obstruction: c(x) is not sign-regular (test below) and nonzero crossing coefficients keep appearing for classes of size >= 5 (n=13: 585 of them, with profile sums -65, -286, 286, 117).
5. **Count certificate partitions per word (certificate product).** Fails to count winning words: it counts certificate partitions of a FIXED word; many certificates per word cause overcount (face-decomposition / product theorem is per word).
6. **Linear free-cumulant ansatz kappa_s(q) = a_s + b_s q.** Killed at n=10 (305 vs 300).
7. **Closed form along diagonals A(2k+j,k) = C(2k+j,k-1) P_j(k) with deg P_j = j-1.** Holds j<=5 (j=4: 2 checks, j=5: 1), breaks at j=6.
8. **Guess a P-recursive / algebraic generating function from data.** Underpowered: with 16 terms (n<=15) a recurrence of order r and degree d needs (r+1)(d+1) < ~14. Control: even for q=2 (known rational) no recurrence with order<=4, degree<=2 was found, so the null results for q=3 say nothing. Needs n>=25 or a structural ansatz. (See Part B idea 9.)
9. **Dyck/Catalan bijection for the whole count.** Fails: the counts are not Catalan-shaped beyond the first diagonals (j>=3 diagonals are not hypergeometric products; P_4, P_5 have no rational roots).
10. **Reduce to heavy faces and recurse.** Done in Lean (winning_iff_heavy_face_decomposition) but the reduction still requires counting heavy-face patterns whose certificates are not unique; the "empty-skeleton" case is as hard as the original (GPT's obstruction report).

Also tested and negative: sign regularity. Computed for n=8..11, sign(c(x)) is NOT determined by parity of n-|x| (n=10: 215 positive/125 negative on even parity), so the join semilattice is not geometric (a geometric lattice has alternating Mobius signs and no zeros).

---------------------------------------------------------------------
## Part B. Creative lenses (each with a translation, a test, and a kill condition)

### B1. Large-N matrix models / planar diagrams  [physics; strongest analogy]
Translation: NC partitions with block sizes 2 and 3 are planar Feynman diagrams of a phi^2 + phi^3 matrix model; the free cumulants kappa_s(q) are the connected planar vertex functions; crossings are non-planar (higher genus). q plays the role of N (a colour sum gives a factor q per loop: q^{falling k}).
Prediction: T(q,n) should have a genus expansion where genus-g terms are suppressed by q^{-2g}-like powers; our law "q^j coefficient of kappa_s vanishes for s<5j (j>=2)" is exactly "the first non-planar correction needs 5j edges". Genus = the crossing complexity.
Test: write kappa_s(q) = sum_j gamma_j(s) q^j and look for an exact generating function in s for each fixed j (the j=1 row is the planar skeleton: sequence 1,1,-1,-4,-1,15,23,-41 from cumulants.py). Check whether gamma_1(s) is algebraic (it should be a planar free-probability series) by guessing an algebraic equation; then j=2 as a "torus" correction. Kill: gamma_1(s) not algebraic of low degree.

### B2. Temperley-Lieb / Brauer / planar algebras and Kauffman bracket  [low-dimensional topology]
Translation: NC pair partitions = TL diagrams; blocks of size 3 = trivalent vertices (Fuss-Catalan / SU(2) spider with a 3-vertex); crossings = braid/Brauer generators. Winning = word can be "planarly contracted to the empty diagram".
Test: model winning words as a contraction of a delta-tensor network on q colours; compute the dimension of the span of certificate states in (C^q)^{tensor n}. If dim(span of certificate tensors) = number of winning words with a clean formula, then T(q,n) is a dimension of an invariant space (representation-theoretic closed form, possibly P-recursive). Kill: dimension != number of winning words for q=3, n<=8 (cheap in SymPy).

### B3. Random-matrix / Wigner-semicircle moments and free independence
Translation: the moment-cumulant formula m_n = sum over NC(n) prod kappa already holds for T(q,.); ask whether T(q,.) is the moment sequence of a positive measure for each q (Hankel positivity). If yes, a spectral measure exists and orthogonal polynomials give a three-term recurrence (Jacobi parameters), the usual route to P-recursion.
Test: Hankel determinants of (m_n) for q=2,3,4 up to size 7 (15 terms). Kill: a negative Hankel determinant.
**RESULT (Claude, local exact arithmetic, rows n<=15): KILLED.** Hankel determinants of m_n=T(q,n), sizes 1..7: q=2: 1,2,0,-8,-16,160,-5184; q=3: 1,3,9,-54,-2916,-44712,828144; q=4: 1,4,32,192,-48384,... The size-4 determinant is negative for q=2 and q=3, so T(q,.) is not the moment sequence of a positive measure. (A signed measure or a different normalisation, e.g. cumulant-shifted, is not excluded.)

### B4. Statistical mechanics: partition function and zeros  [physics]
Translation: sum over k of A(n,k) q^falling k is a partition function Z_n(q); chromatic-polynomial-like. Chromatic polynomials have well-studied zero loci and transfer-matrix structure.
Test: zeros of Z_n(q) (n<=15) in the complex q-plane; do they accumulate on a curve (Beraha-Kahane-Weiss) with a limiting density? Accumulation on a curve passing near a real q0 signals a phase transition/critical q (maybe q=4 Beraha-type), which would tell us which q have algebraic gf. Kill: no pattern.

### B5. RNA secondary structure and pseudoknots  [biochemistry; closest real-world analogue]
Translation: sequence = word; a certificate = a base-pairing (secondary structure) in which paired positions carry the same letter, with pairs and base triples allowed and no pseudoknots; "winning" = sequence can be completely folded. Pseudoknots = crossings. Counting sequences compatible with at least one structure = the "neutral network" / designability / inverse-folding counting problem; inclusion-exclusion over structures is standard there too.
Test: search RNA combinatorics (Schmitt-Waterman, Reidys, Hofacker, Stadler: compatible sequence counts, "sequence-structure" generating functions, canonical structures) for the enumeration of sequences admitting a perfect structure over a k-letter alphabet with identical-letter pairing; compare their counting recurrences against rows.txt. Also check the pseudoknot hierarchy (genus 1 pseudoknots = our crossing joins) against the classes-of-size->=5 threshold: in RNA, minimal genus-1 H-type pseudoknot needs 4 base pairs spanning two stems; ours needs two crossed classes of size 5. Kill: no matching sequence in the literature and no structural parallel (still informative).

### B6. Formal language theory: Chomsky-Schutzenberger and ambiguity  [linguistics]
Translation: winning words = language of the grammar S -> e | c S c S | c S c S c S for every letter c (bf_k.c uses exactly this). It is context-free; ambiguity of the grammar = multiple certificates per word (the duplication problem). Chomsky-Schutzenberger: for an UNambiguous CFG, the length generating function is algebraic. T(q,.) algebraic would need an unambiguous grammar or finite ambiguity structure.
Test: (a) compute the number of derivations d(w) per winning word and its distribution (GPT's certificate_partition_count_product is this); (b) test whether the language is inherently ambiguous via pumping-style obstruction; (c) compute the number of NC partitions refining each word and see if the distribution is a product over faces. Kill: heavy-tailed d(w) not factorizable.
Related: determinize the grammar with letter-erasing ("direct grammar determinization" notes already in research/DIRECT_GRAMMAR_DETERMINIZATION_2026_10_28.md).

### B7. Mildly context-sensitive grammars: cross-serial dependencies  [linguistics/philology]
Translation: Swiss-German cross-serial dependencies are the linguistic analogue of crossings; tree-adjoining grammars (TAG) and the RNA pseudoknot literature both use TAG/MCFG for exactly the "genus 1" extension. Our crossing joins with all classes >= 5 could correspond to the "5-dependency" length at which crossing structure is not decomposable.
Test: define the TAG/2-MCFG generated by adding one crossing rule and count its words; compare with T(q,n) corrections gamma_2 (order q^2 terms start s=10).

### B8. Philology: cognate sets and stemmatics  [philology]
Translation: colour class = cognate set; noncrossing = nested correspondences (no loan crossings); winning = the word can be reduced by successive cancellation of paired cognates.
Test: apply to the user's Voynich/Linear A work as a *method*, not a claim: given a candidate word sequence, count how many pair-triple "reduction certificates" it has vs shuffled controls (a z-score). This is an application, not a route to the counting law; flag as optional.

### B9. Algebraic combinatorics: creative telescoping and D-finite closure
Translation: A(n,k) is a double-indexed sequence; the diagonals j=1,2 are hypergeometric; j=3.. are hypergeometric times polynomial for j<=5. Try the *q-dependent* ansatz: T(q,n) satisfies a recurrence with coefficients polynomial in n AND q, fit simultaneously from all rows (many more equations than a single-q fit).
Test: guess P-recursive relations in n with coefficients polynomial in q using rows for q=2..7 jointly (n<=15). Control: q=2 must be reproduced. Kill: no relation of total size < 10 unknown parameters per equation count.

### B10. Poset topology: Mobius functions and discrete Morse theory  [topology]
Translation: c(x) = -mu(0hat, x) on the join semilattice generated by NC 2/3 partitions inside the partition lattice. The crossed-four vanishing (proved) is the statement that the crosscut complex of x has trivial reduced Euler characteristic; the survivors with classes >= 5 should have homology (e.g. spheres of specific dimension), explaining sums like 286 = C(13,3) and 117 = 9*13.
Test: for n=10 (the first 5 nonzero crossing joins, c=-1 each) compute the homology of the crosscut complex (all certificate subsets with join x, as a simplicial complex) with exact SymPy/Smith normal form; look for a sphere. If every nonzero-coefficient crossing join has the homology of a sphere, c(x) = +-1 times the number of "sphere classes" => combinatorial interpretation of c. Kill: torsion or non-sphere homology.

### B11. Information theory / Kolmogorov structure  [information theory]
Translation: a winning word has a short "deletion program" (the certificate). Count words by description length: T(q,n) = number of words whose shortest program exists; the multiplicity of programs (certificates) is the redundancy.
Test: compute the entropy of the certificate-count distribution d(w) over winning words for n<=12; check whether log T(q,n)/n has a limit and whether the limit is the log of an algebraic number (growth rate). Observed ratios T(q,n+1)/T(q,n) at n=14: q=2: 2.087 (falling, plausibly toward 2), q=3: 3.045 (rising), q=4: 3.705 (rising); so the growth constant rho(q) for q>=3 is not read off from n<=15. Use these as a growth-constant fingerprint: if rho(q) is algebraic of low degree, we gain a target.

### B12. Quantum / interference reading of the signed expansion  [SPEC]
Translation: OR over certificates becomes a sum with signs (Mobius); crossed-four cancellation looks like destructive interference between amplitudes of pairing (separated) and (nested) pairings. In quantum terms: a "state" |w> = sum over certificates of signed amplitudes; the coefficient c(x) is a net amplitude on join x. Cancellation is forced when two paths related by a local move differ by a sign.
Test (concrete, no physics needed): look for a sign-reversing involution (a "Gessel-Viennot / Lindstrom" style) on certificate subsets for every x with a crossed 4-class; GPT's Lean proof is algebraic, so an involution proof would give a *bijective* explanation and probably generalize to classes of size 5 with a small defect. Kill: no uniform involution exists (we found 10 n=10 exceptions without a single redundant atom).

### B13. Biochemistry: enzyme cascades / kinetic proofreading  [SPEC]
Translation: sequential cancellation of adjacent equal letters resembles a stochastic reaction network; a maximal-run deletion is an irreversible step. Winning = the network reaches the empty state with positive probability under some schedule; counting = measure of attractor basin.
Test: none concrete beyond the Markov-chain view; recommended to skip unless B5/B6 give traction.

### B14. Number-theoretic fingerprints
Test: reduce A(n,k) modulo small primes (2,3,5,7) and look for Lucas-type / automatic structure; also check p-adic valuations of the diagonal entries (e.g. 28, 300, 2310, 15015, 88088 have factors 7, 5, 11, 13 pointing to binomials; P_j values with large prime factors of size near n are a binomial signature). Cheap, and can show *why* j=6 differs (new prime factors).

---------------------------------------------------------------------
## Part C. Suggested order (my guess at information per effort)
1. B10 (homology of crosscut complexes, n=10) and B12 (involution): explain c(x), directly extend the proved lemma.
2. B1/B3 (planar expansion of the cumulants; Hankel positivity): cheap, uses existing data.
3. B5 (RNA literature) and B6 (grammar ambiguity): could identify the right known framework or prove it is novel.
4. B9 and B14: scale the data with the q-joint recurrence guess and arithmetic fingerprints.
5. B4, B11, B7: exploratory.
Please reply by pushing a branch research/gpt-ideas-review-20261029 with, per idea: tested/not, result, CI run id, label.

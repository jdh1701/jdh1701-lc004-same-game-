# Canonical paths, a certified enumerator, and a four-way obstruction

Continuation of the 17 October 2026 checkpoint. Published base commit:
`25963923aa96a21bfc685b25c125d7dd94a7e16d`. Its Git tree is exactly the
approved local checkpoint `0f6fd5cd15e714997c64f89d12412a9c65f1624e`.
No merge into main is part of this campaign.

**Outcome:** the complete index sequence of a unique solution is now proved
in Lean; a finite successful-path enumerator has a proved correctness
specification; an explicit four-way ambiguity obstruction has kernel-checked
certificates. Exact weighted unique-word counts extend to q=3,n=22 and
q=4,n=18. The full multicolour winning-string enumeration is still unresolved.

## Formal results

All statements below concern the existing executable Boolean run-state
semantics. No palette-size restriction is needed for the first two results.
The ordinary-cell / Boolean commuting theorem remains a separate obligation.

### 1. The entire unique path is fixed by the run count

`LC004/UniqueCanonical.lean` proves:

```lean
theorem unique_successful_path_eq_medianPath
    {s : RunState} {moves : List Nat}
    (hn : Normalized s) (hu : UniqueSuccessfulPath s)
    (hp : SuccessfulPath s moves) :
    moves = medianPath s.length
```

Here `medianPath (2m+1) = [m,m-1,...,0]`, and `medianPath 0=[]`.
The companion length theorem gives exactly `(s.length+1)/2` deletions.
The empty source is handled explicitly. A successful child inherits
uniqueness; each step removes one or two runs. Combining that length change
with the proved median necessity forces the descending index sequence.

This is a necessity theorem under uniqueness. Success of the canonical
candidate **does not** establish uniqueness. The four-way counterexample
below provides a checked negative control.

### 2. A correct, exact finite path enumerator

`LC004/CertifiedPaths.lean` defines `pathSetFuel n s` as a finite **set** of
index sequences. Finsets suppress duplicate derivations. It proves

```lean
p ∈ pathSetFuel n s ↔ SuccessfulPath s p ∧ p.length ≤ n
```

and, using the proved maximum path length `s.length`, defines
`solutionPaths s := pathSetFuel s.length s` and proves

```lean
p ∈ solutionPaths s ↔ SuccessfulPath s p
UniqueSuccessfulPath s ↔ (solutionPaths s).card = 1
```

There is no unproved solver-correctness hypothesis or external oracle in
these statements. The algorithm is exhaustive and can be exponential;
this is a correctness result, not a new efficient general solver or a
new counting formula. The optimized Python solver is independently
implemented, not silently identified with this Lean implementation.

### 3. A certified four-way interaction

`LC004/FourWayCertificate.lean` fixes the run-colour skeleton

```text
0 1 0 2 1 2 1 2 0 1 0
```

The middle run, index 5, is heavy. Four other runs, indices **1,3,6,8**,
are optionally heavy; all remaining runs are light. A four-bit mask selects
the options. The Lean certificates prove:

| Active optional runs | Certified successful path count |
|---|---:|
| Any proper subset of those four runs (all 15 masks) | 1 |
| All four runs | 91 |
| All four runs, counting only paths with at most six deletions | 1 |

The sole short path is `[5,4,3,2,1,0]`; an alternate path is
`[1,1,3,2,2,1,0]`. Thus a unique shortest solution can coexist with many
successful complete paths.

The shortest ordinary representative of this **chosen** run-state witness
is the 16-cell word `0110221221120010`. Lean checks its encoding equals the
full-mask run state. Independent ordinary-cell and run-state Python solvers
agree on all 16 mask cases, including the full count 91.

The card computations use kernel reduction (`decide`), not a native
computational shortcut. Each proper mask's finite cardinality is connected
to universal path uniqueness by the proved enumerator specification.

This refutes an ordinary conflict graph model in which uniqueness means
that the active optional heavy runs form an independent set. Every active
pair, and every active triple, is permitted in this example, while their
four-run union is not. A description using only forbidden pairs or triples
of these variables therefore cannot capture the property. It does not
exclude a richer graph representation with additional context states.

## Executed counting extension

`unique_weighted.py` enumerates normalized palindromic colour skeletons
with a heavy centre, using first-occurrence colour representatives. It does
**not** assume the rejected pairwise criterion. For every candidate it uses
the exact game-tree solver to distinguish one successful path from more
than one. Run lengths are restored using `z` for a singleton and
`z²/(1-z)` for a heavy run, and colour classes receive falling-factorial
label weights. Reversal is not quotiented.

| Palette | Raw lengths | Canonical candidate states | Observed runtime |
|---:|---|---:|---:|
| 2 | 0–22 | 14,328 | 0.38 s |
| 3 | 0–22 | 921,413 | 171.41 s |
| 4 | 0–18 | 175,361 | 15.40 s |

These are finite exhaustive candidate domains, not samples. They overlap
and share solver subproblems; their totals are not independent evidence.
The q=3 calculation does not iterate over all `3^22` raw strings. Its
coverage uses the proved necessary run-skeleton structure and exact
positive-integer run expansion weights. The Python enumeration itself,
and the raw-word semantic correspondence, are not claimed Lean-verified.

All overlaps match the earlier direct raw census and the independent
unfiltered orbit-polynomial census through n=12. Further old-branch counts
at q=3,n=13 and q=4,n=10,11 also match. Binary coefficients agree with the
candidate weighted formula through n=22.

Selected **unique-path** raw-word counts:

| n | q=3 | q=4 |
|---:|---:|---:|
| 13 | 13,521 | 79,912 |
| 14 | 30,165 | 206,332 |
| 15 | 67,281 | 532,708 |
| 16 | 149,985 | 1,375,072 |
| 17 | 334,125 | 3,548,776 |
| 18 | 743,625 | 9,156,244 |
| 19 | 1,653,333 | Not computed |
| 20 | 3,672,261 | Not computed |
| 21 | 8,149,017 | Not computed |
| 22 | 18,068,241 | Not computed |

Full coefficients and run-orbit weight tables are in `data/unique_q*.json`
and the companion CSVs. These count the unique-path subclass, not all
winning words.

## Discriminating failure and its correction

Initial tests checked 38,416 singleton, pair and pair-free triple choices
over specified three/four-colour skeleton ranges. No triple counterexample
appeared. That result did not validate the pairwise graph hypothesis.

An independent-set polynomial calculation then compared graph predictions
against the independently enumerated full flag distributions. At eleven
runs with three colours and four heavy outer runs, the graph predicted 984
unique orbits; the actual count is 974. The resulting four-way witness was
reduced and certified in Lean. This is why the successful triple checks
must be retained alongside the later falsification.

The saved graph test stops at the first mismatching shell size and selects
the smallest heavy-set size there. It does not prove global minimality over
all words or all palettes. The certificate proves inclusion-minimality
within the four optional positions of the exhibited skeleton.

## Verification and provenance

* The published base passed GitHub Actions run **39025601875**, including
  the root Lean build and independent Python solvers, on a normal runner.
  This independently removes reliance on the local process-path wrapper
  for the base proof. Status and literal job logs are saved here.
* The new root imports `UniqueCanonical`, `CertifiedPaths` and
  `FourWayCertificate`. The final local build exited 0.
* Final axiom printouts report only `propext`, `Classical.choice`,
  `Quot.sound`. Local builds retain the previously documented process-path
  compatibility wrapper; it does not modify proof checking.
* Static source scans cover all 74 project Lean files, including files
  outside the default import closure. No holes, project axiom declarations,
  unsafe overrides or native computational tactics were found.
* Failed proof attempts remain separately labelled in the logs. Their
  error-recovery terms are not certificates of successful verification.
* A normal-runner workflow checks the new proofs and the finite certificates.
  A configured workflow is not itself a completed run; the final GitHub
  result must be inspected separately.

## Novelty and next experiment

The source/priority register in the parent checkpoint remains applicable.
Additional searches for Clickomania/Same Game unique indexed paths, binary
uniqueness and conflict graphs found no exact match, but search precision
was poor and many hits were unrelated. No priority claim follows from that.
The exact enumerator is a new formalization here of a standard exhaustive
method. The canonical-path consequence and four-way certificate are precise
project advances with unresolved mathematical priority.

The binary classification still has its written paper argument and finite
support, not a universal Lean counting proof. The full q>=3 winning-string
enumeration and ordinary-word commuting theorem remain open in this project.

The most informative next structural test is whether inclusion-minimal
ambiguity sets can have unbounded size for a fixed three-colour palette.
The four-way certificate rules out simple pair/triple-only models but does
not settle whether a finite higher-order description exists.

## Reproduction

From the repository root, using the pinned toolchain and dependency manifest:

```sh
lake build
lake env lean research/checkpoint_2026_10_17/canonical/PrintAxioms.lean
python3 research/checkpoint_2026_10_17/canonical/unique_weighted.py --q 2 --nmax 22
python3 research/checkpoint_2026_10_17/canonical/unique_weighted.py --q 3 --nmax 22
python3 research/checkpoint_2026_10_17/canonical/unique_weighted.py --q 4 --nmax 18
python3 research/checkpoint_2026_10_17/canonical/flag_conflicts.py
python3 research/checkpoint_2026_10_17/canonical/graph_predict.py
```

The graph comparison uses the saved weighted results, so run enumeration
first. Resource use grows with the finite state space. No background work
after the session or fixed-size transfer-matrix solution is claimed.

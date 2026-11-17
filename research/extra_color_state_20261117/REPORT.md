# Extra-base-color refinement: a certified finite-model comparison

17 November 2026. Based on Claude review PR55 at
`0990b0e9a86a0adf78bdbf20a78bcceeafae4d39`. This is an original bounded
computational experiment, not a solution of Same Game, a new uniform-density
proof, or a Lean theorem. No existing source/certificate is replaced.

## Result

Tracking the next-to-last base color reduces the uniform-input worst-case
average drift, but does not make it negative for the policy tested:

| Finite abstraction | Exact interval, denominator 3,000,000,000 | Approximation |
|---|---|---|
| Original, adversarial b at every step | [138287869, 138287874] | 0.046095957 |
| Extra color, adversarial b only on pops | [132338197, 132338202] | 0.044112733 |

The intervals are disjoint (about 4.30% improvement), and both are strictly
positive. Unlike the earlier floating-point diagnostic, these intervals have
integer Bellman subsolution/supersolution certificates replayed by a separate
standard-library checker. They rule out a strictly negative uniform potential
**for the specified finite max-adversary models**, not for the actual base
process, a different witness policy, larger state memory, or Same Game itself.

## Why storing one extra color is not full closure

A state is `(i,b)`, where `i` is one of 23,129 retained-suffix controls and
`b in {1,2}` is the next-to-last base color after normalizing the last to 0.
This gives 46,258 states. For each existing table edge we select the
lexicographically first valid `(new base prefix, color permutation)` witness.
A non-pop determines the successor's stored color. A pop (`r=-1`) exposes an
older base color, which the finite state does not retain. Both proper colors
must remain possible. The adversary may choose this color **after** seeing
the incoming letter; this is a conservative relaxation of a real hidden base,
not an independence assumption about its actual colors.

Concrete obstruction: state 0 is `{empty}`. With `b=1`, input 0 gives target
state 1 `{empty,1}` and `r=-1`. Bases `010` and `210` have identical stored
state, but become bases `01` and `21`. The valid relabeling maps new 0 to old 1
and new 1 to old 0. Their new next-to-last colors are respectively 1 and 2.
Thus a deterministic successor based only on `(i,b)` would be unsound.

Of the 138,774 edges, 115,712 now have determined successors; 23,062 retain
this pop uncertainty. Semantic witnesses were verified for all edges and for
both possible older colors (277,548 three-letter-base cases). Each witness
preserves the older prefix, so the same local construction lifts to longer
bases. This is a paper argument plus finite checks, not formal verification.

Lexicographic witness selection is a fixed policy choice, not optimization
over every admissible relabeling or retained subset. Its failure to yield
negative uniform drift does not rule out improved choices.

## Exact certificate argument

Let `T` be the finite uniform-input Bellman operator. In the original model,
`T h(i) = max_b sum_a [r(i,b,a)+h(j(i,b,a))]/3`. In the refined model,
`T h(i,b) = sum_a [r(i,b,a)+max_{t in allowed(i,b,a)}h(t)]/3`.
Allowed successors are singletons for non-pops and the two possible stored
colors of the prescribed target control for pops.

Both operators are monotone and additively homogeneous. If
`l <= T h - h <= u` componentwise, iteration gives
`h+n*l <= T^n h <= h+n*u`. Hence every initial state's optimal long-run
average-reward lower/upper limits lie in `[l,u]`; irreducibility is not needed.
The finite bounded potential disappears after division by n. A positive
lower endpoint excludes a strictly negative supersolution in that finite
model. It does **not** lower-bound the real base process's drift: the abstract
adversary can invent older colors inconsistent with a real stack history.

NumPy relative value iteration discovers potentials; rounding them to
integers at scale 1,000,000,000 is only a candidate-generation step.
`check_exact.py` reconstructs all semantic witness choices directly from the
pinned table and evaluates the two operators with arbitrary-size Python
integers. It imports neither NumPy nor the experiment. The exact extrema,
not convergence tolerances or floating-point values, establish the intervals.
`exact-check.json` records these extrema and both potential file hashes.

## Regression and soundness checks

- Both existing tilted certificates lift unchanged by duplicating each old
  potential over the two stored colors. Their worst exact drifts remain
  `-3041932/2800000000` and `-304542622/31102873100000000` respectively.
  All 46,258 inequalities per certificate pass in the new abstraction.
- Both original standalone semantic/integer audits were rerun and pass;
  receipts are `baseline-original.json` and `baseline-refined.json`.
- Exhaustive ternary words through length 10 check 88,572 prefix transitions:
  the retained-policy stacks always form a subset of the full fusion support;
  every deep transition matches the augmented successor set; every exact
  fusion acceptance agrees with an independent maximal-run recursive game
  solver. Winning counts for lengths 0..10 are
  `1,0,3,3,15,33,105,297,879,2631,7833`.
- The shallow-base policy keeps the lexicographically first legal successor
  stack and resets to control 0. This is safe but not claimed optimal.
- Small-case checks do not prove equality of retained-policy and actual-game
  acceptance. Retained supports are deliberately conservative.

## Reproduction

From repository root, Python 3.12.14, NumPy 2.3.5 (SciPy not used):

```sh
python research/extra_color_state_20261117/experiment.py --small-n 10 --iterations 12000
python research/extra_color_state_20261117/check_exact.py
cd research/entropy_certificate_20261111
python audit_certificate.py prefix9-1.txt tilted10-9.certificate.txt
python audit_certificate.py prefix9-1.txt refined-bias.certificate.txt
```

The exact checker requires only Python's standard library and saved text
potentials. Discovery iterations were 242 (old) and 246 (refined), each
stopping at residual span below 1e-10; runtime and floating outputs are not
certificate premises. The model hash is
`9e2b870282b506b1e730d96faf57179cf54b719ee7d1b2cbebfb058cc37500cb`.
The included CI workflow replays the exact checker and both baseline audits.
Its existence is not a claim that a hosted run has passed; check the exact
published commit's workflow status separately.

## What this changes and next bounded experiment

The naive claim that one extra color removes all adversarial uncertainty is
false. The sound partial refinement improves drift but remains positive.
The original biased entropy bound survives unchanged; no stronger growth
bound is claimed. Exact all-length enumeration and positive uniform density
remain open. No new Lean compilation was attempted.

The next discriminating experiment is to optimize among **all valid witness
choices** in this augmented model before increasing state count. If that
still fails, retain a longer base suffix and expose uncertainty only when
that suffix is popped past its boundary. Such refinements must retain an
honest adversarial boundary or prove a different closure mechanism; a finite
suffix alone does not remember an unbounded stack.

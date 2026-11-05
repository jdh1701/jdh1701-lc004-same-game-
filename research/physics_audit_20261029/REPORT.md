# Physics, nature, economics and coding audit

Scope: our Lean model is a one-dimensional finite word with chosen deletion
of an entire maximal monochromatic run of length >=2. There is no replenishment,
2D falling-column mechanism, automatic match cascade, or strategic block agent.
This distinction is essential when assessing claims about Blockomania variants.
The sources below support related models, not a proved SameGame equivalence.

## Assessment of requested connections

| Proposal | Assessment and usable content |
|---|---|
| Spin glasses | A landscape analogy, not a demonstrated isomorphism. Sherrington-Kirkpatrick uses fixed spins with random couplings; a spin flip preserves variable count, our deletion reduces it. Quenched disorder means disorder held fixed during the relevant dynamics, not simply sudden compaction. Useful direction: signed partition functions, higher-order interactions, and their zero sets. |
| BTW sandpiles / SOC | Exact equivalence under the natural move identification is KILLED by order dependence below. Our game has neither slow driving nor automatic threshold toppling. Avalanche-like visual behavior does not establish critical exponents or SOC. Dhar distinguishes Abelian and non-Abelian variants. |
| Crystal defect annealing | A qualitative transport analogy. Dislocation climb involves absorption/emission and diffusion of point defects plus energetic/kinetic laws, not deterministic deletion and left compaction. No weight-preserving correspondence supplied or found in the inspected sources. |
| Market clearing / fire sales | Price-mediated feedback is real. Cifuentes et al. use mark-to-market losses, illiquid demand and solvency constraints. Regulatory balance-sheet feedback is not literal spatial gravity or proof that banks become neighbors by sliding. A network contagion model would require explicit exposures, prices and transition laws. |
| Coalition formation / matching | Hedonic coalition models specify preferences over fellow members and stability conditions. Our blocks have no utilities or consent decisions; one player controls deletion. Partition-lattice language is shared, but stability theorems do not automatically enumerate our winning words. |
| Mechanism design / hidden blocks | Hidden stochastic replenishment produces a different decision problem. A stochastic transition rule and observation model could define a POMDP, but mechanism design additionally needs agents, incentives and information structure. The game mechanics do not demonstrate sunk-cost bias; that needs behavioral evidence. |
| Chromatin / epigenetics | Real recolourable-polymer models couple 3D folding to writing/reading marks. Silencing is not deletion of DNA or physical removal of a methylated gene segment. No support found in inspected primary sources for the claim that identical puzzle reductions simulate these dynamics. |
| Burst error correction | Promising structural language after correction: deletion removes a symbol and loses synchronization; erasure retains a known missing position. Our move is a constrained burst deletion, homogeneous and maximal, repeated adaptively. Standard burst-deletion code results handle arbitrary allowed bursts and decoding, so require an additional correspondence before use for winning-word enumeration. |
| Dynamic redistricting | ReCom operates on partitions of fixed geographic units using spanning-tree proposals. It does not delete precincts and shift physical adjacency or move state boundaries. Graph partitions are a useful shared abstraction; the asserted identical compaction mechanics are unsupported. |

These are scoped assessments. Search failures are not proofs that no connection
exists. No broad novelty or exhaustive-literature claim is made.

## Primary sources inspected

Sherrington & Kirkpatrick (1975), DOI 10.1103/PhysRevLett.35.1792,
https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.35.1792 (abstract).
Bak, Tang & Wiesenfeld (1987), DOI 10.1103/PhysRevLett.59.381 (abstract).
Dhar (1998/1999), https://arxiv.org/abs/cond-mat/9808047 (abstract).
Cifuentes, Ferrucci & Shin (2005), DOI 10.1162/jeea.2005.3.2-3.556 (abstract),
https://www.bankofengland.co.uk/working-paper/2005/liquidity-risk-and-contagion .
Bogomolnaia & Jackson (2002), The Stability of Hedonic Coalition Structures,
https://www.sciencedirect.com/science/article/pii/S0899825601908772 (abstract).
Michieletto, Orlandini & Marenduzzo (2016), https://arxiv.org/abs/1606.04653
(abstract), DOI 10.1103/PhysRevX.6.041047.
Schoeny et al. (2016/2017), https://arxiv.org/abs/1602.06820 (abstract).
DeFord, Duchin & Solomon (2021), https://hdsr.mitpress.mit.edu/pub/1ds8ptxu/release/5
(abstract and graph-partition setup).
Dislocation-climb review: DOI 10.1146/annurev-earth-031621-063108 (abstract/snippets;
secondary review used only to triage, no new theorem based on it).
Algorithmic Cluster Expansions for Quantum Problems (2024), DOI
10.1103/PRXQuantum.5.010305 (abstract/search excerpt only; author PDF fetch failed).
The Velenik cluster-expansion PDF fetch was blocked; no full reading claimed.

## Concrete mathematical result

PROVED-PAPER (elementary derivation, no novelty claim): for a nonempty certificate
family C below a nonbottom target p, put a hyperedge on each inclusion-minimal
subset whose join is p. Its independent sets are exactly the nongenerating
subsets. Thus its independence/partition polynomial
  Z_H(t) = sum_{S independent} t^|S|
satisfies c(p)=Z_H(-1), by the alternating-sum identity from the prior checkpoint.
This is an exact hard-constraint hypergraph gas at a signed activity, NOT a
positive probability measure or a claimed spin-glass dynamics equivalence.

For a chosen vertex v, split independent sets according to whether v occurs:
  Z_H(t)=Z_{H_out}(t)+t Z_{H_in}(t).
Both residual hypergraphs have vertex set V minus v. H_out retains only edges
not containing v; H_in removes v from every edge. Empty forbidden edge means
partition function zero. Inclusion-redundant hyperedges can be removed.
This proves the deletion/contraction recursion implemented in probe.py.

VERIFIED-COMP: on the prior 9- and 12-certificate graph counterexamples, the
full coefficient polynomials from memoized recursion match direct enumeration
coefficient by coefficient. Both evaluate to 2 at -1, correctly restoring the
higher-order terms. Recursion used 29 and 46 memoized states respectively.
IMPORTANT: building the hypergraph still used 512 and 4096 subsets. These
figures do not establish an overall speedup or solve arbitrary-size enumeration.

The zero example has Z_H(t)=(1+t)^4. Consequently log Z_H cannot be analytic
at t=-1. A cluster expansion about zero is not automatically valid at our
required activity. Any convergence/analytic-continuation argument must handle
these zeros and signed cancellations explicitly. Ordinary logarithmic cluster
coefficients are also not automatically the free cumulants already defined.

VERIFIED-COMP / explicit move witness: 00110 has terminal outcomes empty and 0.
Delete 11 first: 00110 -> 000 -> empty. Delete initial 00 first:
00110 -> 110 -> 0. Both are legal maximal-run sequences. Therefore the natural
order-independent stabilization analogy with Abelian sandpiles fails.

## Next and Claude handoff

Use the hypergraph recursion as the exact computational target. Derive minimal
generating hyperedges directly from ordered certificate overlaps, avoiding the
full powerset; test bounds on rank, separator size or incidence-treewidth.
Only after proving such a structural bound should we claim efficient transfer
matrix / variable-elimination enumeration. Burst deletion suggests tracking
boundary synchronization states; prove their sufficiency rather than assuming it.
No new Lean theorem, Sage run or direct Claude invocation occurred this pass.

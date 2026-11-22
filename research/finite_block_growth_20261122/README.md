# LC004 finite blocks and height caps

Use the LC004 project with Lean 4.19, Mathlib v4.19.0, and compiled LC004.FusionStack and LC004.LabeledJoinEnumeration. Copy the three Lean sources into its root and run:

    mkdir -p /tmp/lc004-block
    lake env bash -c 'export LEAN_PATH="$LEAN_PATH:/tmp/lc004-block"; lean -o /tmp/lc004-block/RawGrowth.olean RawGrowth.lean && lean -o /tmp/lc004-block/AdaptiveRates.olean AdaptiveRates.lean && lean FiniteBlock.lean'

Theorem full_iff_finite_blocks uses the raw maximal-run labeled count. Concatenation is injective on pairs with prescribed lengths. Every length at least two has a winning word, so the argument handles residual lengths, including the fact there are no length-one winners. For each 1 < r < 3 it suffices to have some positive k with W(k) ≥ r^k. No construction of all those witnesses is claimed.

Theorem capped_block_count counts length-m tuples of length-(2H+1) blocks even allowing unrelated stacks at successive boundaries. Every actual capped computation satisfies this weaker condition. Each block excludes the same alternating word, since a proper segment needs endpoint heights totaling at least its length. Thus the upper exponential rate of computations counted by their input words under a fixed cap is at most (3^(2H+1)-1)^(1/(2H+1)) < 3. This does not bound unrestricted winning words from above by any number less than three. The argument concerns an actual height cap, distinct from bounding residual height only at the end of an otherwise unrestricted input.

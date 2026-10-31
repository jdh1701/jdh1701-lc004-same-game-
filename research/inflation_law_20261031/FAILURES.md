# Failures and limits

The first C++ build failed under -Werror due to misleading indentation after
a one-line for loop. Braces and a separate assertion fixed it before execution.
No mathematical or numerical result was inferred from that failed build.

The initial broad hope that the local table alone proves universal preservation
was too strong: its exact four-generator branch has coefficient +1. This is
an abstract conditional branch, not an actual game counterexample. Geometric
exclusion of uncovered adjacent pairs remains unproved.

The 109302102-case extension search is bounded and can count the same pattern
more than once; 40472 is a completion count, not a new n30 enumeration term.

Initial hosted source71825b76, run41175205459: exact job124461212726 passed;
Lean124461212856 failed in the final simplification of the four-generator
lemma. Residual goal was (if a<=p then1 else0)+(1+if a<=p then-1 else0)=1.
The fact hA:a<=p was already proved and was added to the simp argument list.
The local signature/context module compiled, but the full build failed, so
this source was never promoted to PROVED-LEAN and the axiom audit did not run.
The failed declaration's diagnostic sorryAx comes from its unsolved goal;
there is no sorry in source. The compressed full failure log is retained.

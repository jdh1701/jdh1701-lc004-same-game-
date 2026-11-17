# Next finite geometry target

Support-normalized abstract cancellation is green at c799420, CI40973071008.
Read REPORT.md and LC004/FiveClassGeometryBridge.lean. All 252 labelled
interleavings pass independent endpoint-based ten-choice compatibility tests.
Please try to refute that encoding, then formalize its two finite properties:
conservative-majority closure and a row/column cover whenever the two original
five-classes cross. Empty relations are legitimate; only 140 of 242 crossing
relations are nonempty. Unary internal validity can be absorbed into pair
constraints when there are at least two classes. Rank transport is locally
Lean-verified here. Avoid claiming that this already identifies the original
winningJoinCoefficient or enumerates survivors. No new n25 count is claimed.

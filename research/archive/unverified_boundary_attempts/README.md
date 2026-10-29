# Unverified historical boundary attempts

These five files were outside the import closure of LC004.lean at commit
a734a54bebd860cdc3e6ef7f3c9a6a82772c04d2. The successful build at that
commit did not compile them. They contain seven theorem declarations and
are preserved only as historical text, not as part of the active Lean library.

In particular AdjacentLeftIndexZeroExecutable asserts an unrestricted
prefix-stripping identity that is false when deleting the first suffix run
merges across the boundary. LC004/BoundaryContextRegression.lean supplies a
kernel-checked counterexample. No claim is made that the other archived
proof attempts compile. None is a dependency of the terminal theorems.

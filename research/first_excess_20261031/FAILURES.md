# Preserved failures

First positive replay incorrectly asserted that a pattern has the same dihedral
orbit size as its distinguished six-subset. This is false: the subset may have
a stabilizer that permutes the completions. The C++ census uses subset orbit
weights and enumerates ALL completions, so its weighting is unchanged.
Correction: expand every positive completion into its actual pattern orbit,
allow overlap, and check the union cardinality against the weighted count.
The replay assertion failed before any positive verification claim was saved.

Whole-class deletion is not a universal recursion: the complete n16 census
has surviving patterns for which every five-class deletion has coefficient
zero. Exact rows and counts are recorded by the continuation checks.

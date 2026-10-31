# Retained failed route

The proposed shortcut "proper core + connected class-crossing graph + valid
complementary two-layer pair implies exactly two original certificates" is FALSE.

Core labels:

    0 1 0 1 0 2 1 3 2 3 2 3

Rows are three sorted class positions, root, upper endpoint, lower endpoint:

    0 2 4 0 2 4
    1 3 6 3 6 1
    5 8 10 8 10 5
    7 9 11 11 7 9

Expansion gives:

    0 1 1 0 0 1 0 0 2 2 1 1 3 3 2 3 3 2 2 3

The complete Python local-catalogue choice tuples are
(2,0,0,3), (4,2,0,3), (4,2,2,0). There are THREE original certificates;
the original coefficient is zero. `check.py` regenerates and checks the example.
Catalogue numbering here is Python's, not Lean's.

At j=4, 357 connected proper pairs reduce to 249 strong pairs; at j=5,
7473 reduce to 3873. Local validity and undirected connectivity are therefore
insufficient. The final algorithm retains the complete directed SCC test,
and every accepted object is separately checked against its entire original
certificate family.

No j=8 completion is claimed. No closed formula is inferred from the six counts.
The successful original-family replay validates positives; the paper bijection
and search traversal, plus smaller certificate-first censuses, address completeness.

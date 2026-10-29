# Free-cumulant reading of the winning-word counts (2026-10-29)

Status vocabulary follows research/WORKBOARD.md.

Data: `rows.txt` = A(n,k), the number of winning colour patterns of length n with k classes,
n = 2..14 by brute force (independent C enumerator, matches GPT's totals through n = 10),
n = 15 from the face-decomposition counting formula. Rows 16 and 17 were attempted with the
same formula and the process was killed (memory); they are NOT available.

T(q,n) = sum_k A(n,k) q^(falling k) is the number of winning words of length n over q letters.
`cumulants.py` computes the exact free cumulants kappa_s(q) of the moment sequence T(q,.)
(m_n = sum over noncrossing partitions of the product of kappa_(block size)).

Observed (VERIFIED-COMP, n <= 15 only):
* kappa_s(q) is a polynomial in q; its q^j coefficient vanishes for s < 5j for s <= 15
  (kappa_10 first has q^2, kappa_15 first has q^3). Output at s = 8..15:
  8:[0,23] 9:[0,-41] 10:[0,-161,-5] 11:[0,12,-22] 12:[0,827,30] 13:[0,807,403]
  14:[0,-3599,546] 15:[0,-7625,-3285,-35]  (coefficient lists in ascending powers of q).
* CONJECTURE: gamma_j(s) = 0 for s < 5j (crossing components need blocks of size >= 5).
* KILLED: the hypothesis "kappa_s(q) is linear in q". It reproduces rows n <= 9 and fails at
  n = 10 (predicts 305, true 300).

Nothing here is proved in Lean and none of it solves the fixed-q >= 3 counting problem
(OEIS A035617). Novelty is unchecked (OEIS fetch was blocked).

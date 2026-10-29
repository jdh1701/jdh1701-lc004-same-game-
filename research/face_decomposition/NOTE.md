# Face decomposition for one-row Same Game patterns

Status: PROVED-PAPER, VERIFIED-COMPUTATIONAL. Not yet formalized in Lean.
Authors of this note: Claude (Anthropic), for jdh1701. Date: 2026-10-28.
Tracking: claim IDs refer to `research/WORKBOARD.md`.

A(n,k) counts winning colour patterns (unlabeled set partitions of n
positions with exactly k classes, winning under maximal-run deletion),
exactly as `winningColorPatternCount n k` in LC004.

## Statement (claim T)

Classes of size 2 or 3 are *rigid*. Classes of size at least 4 are *heavy*.
Fix a profile: m2 pairs, m3 triples, heavy sizes s = (s1, ..., sr).
Put w = m2 + m3, |s| = s1 + ... + sr, n = 2 m2 + 3 m3 + |s|, k = w + r and
b = n - |s| - w + 1 (the number of faces of the rigid skeleton).
Let Omega_r(z1..zr) be the content generating function of winning words over
r labelled letters (empty word included). Then the number of winning
patterns with this profile is

    W(m2, m3; s) = n! / ((n - w)! * m2! * m3! * b * Aut(s)) * [z^s] Omega_r(z)^b

where Aut(s) is the product of factorials of multiplicities among the heavy
sizes. For w = 0 this reads [z^s] Omega_r / Aut(s). A(n,k) is the sum over
profiles with n cells and k classes.

## Proof

Step 0 (C0). A pattern wins iff it has a noncrossing refinement into blocks
of size 2 or 3 (Biedl et al. 2002, Thm 2; LC004 `raw_max_win_iff_certificate`).

Step 1 (C1, rigidity). A class of size 2 or 3 is a block of every
certificate (LC004 `certificate_small_block_eq_class`). So the rigid classes
form a noncrossing partition R (the skeleton).

Step 2 (C2, face lemma). Two heavy positions are in the same face iff no
rigid class has points on both arcs between them.
Claim: the pattern wins iff R is noncrossing and, for every face F, the word
on the heavy positions of F (global order) wins.
(=>) A certificate block of heavy positions crosses no rigid block, so it lies
in one face; restrict the certificate.
(<=) A block inside one face crosses no rigid block (no rigid block separates
two of its points). Suppose beta in F and beta' in F' (F != F') cross:
a < a' < b < b' with a, b in beta and a', b' in beta'. Some rigid block B
separates a from a'. B separates neither a,b nor a',b', so it lies on one
side of each pair. Its point between a and a' puts B inside arc (a,b) and
inside arc (b',a'), whose intersection is arc (a,a'); this contradicts B
having a point outside (a,a'). Hence R plus the face certificates is a
certificate.

Step 3 (C3, slots). A face touching d circular gaps offers d linear slots,
plus one for the outer face. A face word of length t is cut into p slots in
C(t+p-1, p-1) ways, bijectively. With labelled heavy classes,
S(u,z) = sum_p u^p sum_{winning v} C(|v|+p-1, p-1) z^v = u/(1-u) * Omega(z/(1-u)).

Step 4 (C4, C5). The number of noncrossing partitions of N0 cyclic points of
type alpha and Kreweras-complement type beta is
N0 (l(alpha)-1)! (l(beta)-1)! / (Aut alpha * Aut beta)
(Goulden-Jackson 1992; Krattenthaler-Mueller arXiv:0704.0199 Thm 5).
Rotation preserves type and cotype, so a face with d gaps is the outer face
with weight d/N0. Summing over ordered face sequences, the labelled count is
(w-1)!/Aut(alpha) * [u^N0] D S^(b-1) with D = u d/du (S/u) = S' - S/u.

Step 5 (C6). D S^(b-1) = (S^b)'/b - S^b/u, so the bracket equals
(w/b) [u^(N0+1)] S^b = (w/b) [z^s] Omega^b * C(n, w). Multiply by
w!/(b Aut alpha), divide by Aut(s). QED.

## Corollaries

- K1: r = 0 gives Kreweras: n!/((n-w+1)! m2! m3!).
- K2: one heavy class of size s: count = Kreweras(type) * c_s(b)/b with
  c_s(b) = [z^s](1/(1-z) - z)^b and b = K - s + 1, K = n - k + 1.
- K3: A(2k+2,k) = k C(2k+2,k-1). (Now PROVED-LEAN on the counting branch,
  `winningColorPatternCount_second_diagonal`, CI run 40811399447 at 8d8f647.)
- K4: A(2k+j,k)/C(2k+j,k-1) for j = 1..7:
  1; k; (2k-1)(k+2)/3; (5k^3+17k^2-5k-5)/12;
  (13k^4+85k^3+75k^2-155k+42)/60;
  (38k^6+694k^5+4025k^4+6670k^3-5593k^2-9434k+6840)/(360(k+8));
  (116k^7+2794k^6+23345k^5+72835k^4+20489k^3-187229k^2+21570k+71280)/(2520(k+9)).
  Each profile term is a polynomial in k over (k+j+2)...(k+j+r); agreement on
  40 values exceeds the degree bound, so these are identities.
- K5: A(2k+j,k)/C(2k+j,k-1) = I_j k^(j-1)/j! + O(k^(j-2)), I_j involutions.
  Proof: degree of profile term is m3 + sum floor(s_i/2) - 1, maximal only
  when every heavy class has size 4; top term k^(j-1)/(m3! m! 2^m).
- K6: second coefficients of T(b,m) (OEIS A323844):
  [b^(k-1)] T(b,2k) = C(2k,k) k(k-1)(k-4) / (2(k+1)(k+2));
  [b^(k-1)] T(b,2k+1) = C(2k+1,k-1) (k-1)(k^2-11k-6) / (6(k+3)).
- A323844's conjectured polynomials for m = 12..16 equal the brute-force rows,
  hence are theorems (polynomiality is immediate from the falling-factorial
  expansion).

## Reproduction

    gcc -O2 -o bf bf.c && ./bf 14            # brute-force rows
    python3 fullrows.py                      # theorem rows vs brute force
    python3 diag_formula.py 7 40             # diagonals j <= 7
    cd audit && gcc -O2 -o g1ex g1ex.c && ./g1ex 12   # face lemma, exhaustive
    python3 g4mut.py                         # mutation gate
    python3 g5gj.py 11                       # Goulden-Jackson + rotation gate

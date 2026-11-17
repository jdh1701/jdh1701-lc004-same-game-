# Fixed-content counts W(3,3,r): reproducible script and exact closed form

17 November 2026. Claude. This answers point 4 of [R-2026-11-14](../../coordination/requests/R-2026-11-14.md). That point asked for a preserved script for the (3,3,r) fixed-content counts, and for the domain of the formula (2^(r−3)+1)(r+6)(r+5).

**Definition.** W(3,3,r) is the number of *labeled* words that contain exactly three A's, three B's and r C's and can be erased completely under maximal-run deletion.

## Results

**1. Counts (VERIFIED-COMP).** Two independent methods agree for r = 0…11:
- brute-force enumeration of every word, with an uncapped game solver
- the type-sum method described below

The type-sum method alone extends the counts to r = 40. They are recorded in `results.json`.

| r | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| W(3,3,r) | 72 | 270 | 550 | 1188 | **2340** | **4368** | 7770 | 13248 |
| (2^(r−3)+1)(r+6)(r+5) | 144 | 270 | 550 | 1188 | 2652 | 6006 | 13650 | 30960 |

**2. The old formula is KILLED.** It matches only at r = 4, 5 and 6. It gives 2652 and 6006 at r = 7 and 8, against the true 2340 and 4368, which confirms the Nov 14 report.
- Its domain was the labeled count, since it agrees with these labeled values at r = 4–6.
- It looks like a fit to r ≤ 6. Its exponential term cannot hold, because the true count grows polynomially (point 3).

**3. Exact closed form (PROVED-PAPER, verified for 6 ≤ r ≤ 40).** For every r ≥ 6:

```
W(3,3,r) = (r^6 + r^5 + 15 r^4 + 395 r^3 − 376 r^2 − 3636 r + 18720) / 120
```

The leading term is r⁶/120 = 6·r⁶/6!. The total number of words is 20·C(r+6,6) ~ 20·r⁶/720, so the winning fraction tends to 6/20 = 3/10.

## Proof sketch of the closed form

1. **Cap lemma.** Maximal-run deletion removes a whole run of length ≥ 2, and merging runs adds their lengths. Since min(a+b, 2) = min(min(a,2) + min(b,2), 2), replacing every run length ℓ by min(ℓ, 2) commutes with deletion and merging. So whether a word wins depends only on its capped run sequence.
2. **Type sum.** A word with content (3,3,r) is an A/B pattern p (one of 20) interleaved with 7 C-gaps g₀,…,g₆ summing to r. By the cap lemma, only the types t_i = min(g_i, 2) ∈ {0, 1, 2+} matter. A type vector with s gaps equal to 1 and k ≥ 1 gaps of type 2+ is realized by C(r − s − k − 1, k − 1) gap vectors. With k = 0 it is realized by exactly one gap vector if r = s, and by none otherwise.
3. **Polynomial.** Since s + k ≤ 7, the top argument r − s − k − 1 is ≥ 0 whenever r ≥ 8. There each binomial is a polynomial in r of degree k − 1 ≤ 6. So W(3,3,r) = Σ_{p,t winning} (multiplicity) is a fixed polynomial of degree ≤ 6 for r ≥ 8, and seven values determine it. The script interpolates exactly at r = 8…14, checks every r up to 40, and finds that the polynomial also holds at r = 6 and 7.

The cap lemma and the counting are paper arguments, not Lean. The brute-force method uses no cap, so its agreement for r ≤ 11 independently checks both steps on those cases.

The same argument shows that W(a,b,r) is a polynomial in r of degree ≤ a + b once r ≥ a + b + 2, for any fixed a and b.

## Corollary: WORKBOARD H1 (binary content counts)

H1 conjectures that B(a,b), the number of winning words with a A's and b B's, is a polynomial in b of degree a for b > a. It had been checked for a ≤ 6.

The type sum with a single A-pattern and a + 1 B-gaps gives the following.

- **PROVED-PAPER, for every a ≥ 2 and b ≥ a + 2:** B(a,b) is a polynomial in b of degree exactly a, with leading coefficient 1/a!.
  - When b ≥ a + 2, every multiplicity C(b − s − k − 1, k − 1) is a polynomial, since s + k ≤ a + 1.
  - The only degree-a term comes from the type in which all a + 1 gaps are 2+. Its words have the form BB…A BB…A … BB…, and they win: delete the inner B-runs, then A^a, then the merged B's.
  - So the leading coefficient is 1/a!. As a result B(a,b)/C(a+b,a) → 1.
- **VERIFIED-COMP, for 2 ≤ a ≤ 7:** the same polynomial also holds at b = a + 1, which is the full range b > a that H1 states.
  - Each polynomial is checked through b = 4a + 11, and the type sum agrees with brute force for a + b ≤ 18.
  - A general proof of the b = a + 1 boundary case is open. It reduces to an alternating sum over the gap types with no empty gap.
- **a = 1 is a degenerate exception:** B(1,b) = 0, because a single A can never be deleted.

Examples:

- B(2,b) = (b+2)(b−1)/2 for b ≥ 3
- B(3,b) = (b³ − b + 24)/6 for b ≥ 4

`binary_results.json` has all coefficients for a ≤ 7. Novelty against the literature has not been checked.

## Reproduce

```sh
python3 -I research/fixed_content_333_20261117/binary_content.py 7 | diff research/fixed_content_333_20261117/binary_results.json -
python3 -I research/fixed_content_333_20261117/fixed_content_333.py 11 40 > /tmp/fc.json
diff research/fixed_content_333_20261117/results.json /tmp/fc.json
```

Both scripts use the standard library only. They take about 20 s and 3 s.

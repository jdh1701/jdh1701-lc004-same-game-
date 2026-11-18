# W_n(q) for every alphabet size, n ≤ 20, from binary, ternary and one quaternary term

18 November 2026. Claude. Answers part of R-2026-11-04 Q1 and Q5.

## Result

Status: **VERIFIED-COMP**, derived from PROVED-LEAN theorems. For every n ≤ 20 the count W_n(q) is an explicit integer-valued polynomial in q, so it is known for every alphabet size q.

- n ≤ 19 uses only the 1-, 2- and 3-letter counts.
- n = 20 also uses one published 4-letter term, W₂₀(4) = 18844637356 (OEIS A065237). The polynomials are listed in `results.json` under `W_n_coefficients_in_q_low_to_high`. For example:

```
W_19(q) = 75582 q^9 − 201552 q^8 − 786828 q^7 + 4465152 q^6 − 8818071 q^5
          + 9351192 q^4 − 5891862 q^3 + 2194253 q^2 − 387865 q
```

New sequence terms, if the OEIS has none beyond the terms quoted in the script:

| q | OEIS | known through | new here |
|---|---|---|---|
| 4 | A065237 | n = 20 | none: our n = 19 value matches the OEIS |
| 5 | A065238 | n = 18 | W_19 = 54791363625, W_20 = 235860627145 |
| 6 | A065239 | n = 18 | W_19 = 353580952206, W_20 = 1689824174346 |
| 8 | A065241 | n = 17 | W_18 = 1083678107240, W_19 = 6029850398328, W_20 = 33707710433944 |

The results also give n ≤ 20 for q = 7 and 9–15, and any other q by evaluating the polynomial. The OEIS ranges for q = 7, 9 and 10 (A065240, A065242, A065243) have not been checked yet.

## Why it works

1. **The Lean side.**
   - `labeledWinningCount_connected_expansion` (PR #34) is the free moment–cumulant relation, W_n(q) = Σ over noncrossing π of Π κ_|B|(q), with κ_s(q) = `connectedGameWeight q s`.
   - `connectedGamePolynomial_natDegree_le` and `connectedGamePolynomial_constant_zero` (PR #42, run 41029475200) show that κ_s is a polynomial in q with no constant term and degree ≤ max(1, ⌊s/5⌋).
2. **Degree ≤ 3.** For s ≤ 19 the degree is at most 3, so κ_s is fixed by its values at q = 1, 2 and 3. Those values are the free cumulants of the 1-, 2- and 3-letter counts.
3. **Reassembly.** Putting the moments back together gives W_n(q) for all q. In general, **W_n(q) for every q is determined by the counts over at most max(1, ⌊n/5⌋) letters up to length n.**
   - Kurz (2001) bounded the q-degree of W_n itself by about n/2. The cumulant degree bound n/5 is a different and much stronger statement.
   - As far as the novelty searches so far show, it is new.

## Independent checks

All of these pass in `all_alphabets.py`:

- the 1-, 2- and 3-letter counts are reproduced
- brute force for q = 4 (n ≤ 11) and q = 5 (n ≤ 9)
- the published OEIS terms of A065237 (q = 4, n ≤ 19, not used as input there), A065238 (q = 5, n ≤ 18), A065239 (q = 6, n ≤ 18) and A065241 (q = 8, n ≤ 17)

The OEIS terms were computed by other people by brute force, so their agreement through n = 19 is an independent test of the Lean theorems on real data.

## Scope

- The 3-letter input for n ≤ 20 equals OEIS A035617, so nothing here depends on the single-method values W₂₇ and W₂₈.
- Going past n = 20 needs 4-letter counts for n = 21–24 (κ_s has degree ≤ 4 there), and 5-letter counts from n = 25. Those counts do not exist yet, and `fusion_count.cpp` handles only 3 letters.
- **This does not solve A035617.** It transfers what is known for 2 and 3 letters to every alphabet size.

## Reproduce

```sh
python3 -I research/all_alphabets_20261118/all_alphabets.py | diff research/all_alphabets_20261118/results.json -
```

Standard library only; about 12 s.

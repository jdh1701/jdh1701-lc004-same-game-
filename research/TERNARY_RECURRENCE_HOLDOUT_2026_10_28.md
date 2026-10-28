# Same Game sequence-guessing falsification
Date: 2026-10-28. Not a general impossibility proof.

Input: published OEIS A035617 length 0..25 counts for q=3 (26 exact terms). Fit homogeneous constant-coefficient linear recurrences of order 1..9 over rationals to terms with indices <18; validate unseen indices 18..25.

Observation:
Orders 1..8: no exact recurrence fitting all training constraints.
Order 9: a unique rational-coefficient fit exists for the training terms, but it fails on EVERY held-out term (n=18..25).
This DOES NOT rule out larger-order recurrences, polynomial-coefficient recurrences, or other analytic formulas. It only falsifies these specific low-complexity recurrence guesses at the tested prefix.

Research consequence: avoid mistaking interpolation for discovery; use direct structural transitions and explicit overlap corrections, with held-out verification and primary-source comparison.

Source: https://oeis.org/A035617
Program: research/ternary_recurrence_holdout_2026_10_28.py

The general q>=3 counting problem remains unsolved; this is a negative discriminating experiment, not a breakthrough.

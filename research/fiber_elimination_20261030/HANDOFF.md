# Resumable handoff

Continue from branch `proof/class-cut-five-row-20261030`, stacked on PR38
`research/ten-attacks-20261030`, base c6f719c08d519e0656ce6b035c69bbe143d74e46.
Exact source and hosted checks are in receipts.json. Read REPORT.md first.

New formal entry points:
- `winningJoinCoefficient_eq_class_cut_face_sum`: all patterns, classwise cuts.
- `original_certificate_unique_five_row`: local certificate row is unique.
- `winningJoinCoefficient_five_rows_class_cuts`: projection minus five links,
  arbitrary sizes in the other classes.
- `faceAlternatingSum_zero_of_dominant_row`: structural cancellation certificate.
- `winningJoinCoefficient_remove_free_interval`: cancel a whole free Boolean
  interval; `facetFaces_remove_free_interval` proves the sparse facet update.

Next substantive proof target: characterize row families produced by actual
mixed-pattern geometry, especially when a projection equals a row or collapses.
The finite (5,6) census now has two explicit mechanisms (33+11) that can be
transported through cyclic symmetries or formalized as finite original cases.
The larger ambition is a counting recurrence on these row families that avoids
merely restating the full pattern enumeration. No such closure theorem yet.

Repository reconciliation: PR39, source81bca891be8f9f7534444a3fb3cbc9073171af4a,
run41002449977 SUCCESS, already resolves all32 former skips. Do not re-propose
profile(9,9) word001100000001111111 as unresolved: it has a verified collapse.
Its 34-vertex/864-facet core has54528 faces and no elementary free pair with a
lower face of dimension<=2. Use this as a constraint on proposed uniform rules.
The other branch's counts overlap ours and must not be added. See REPORT.md.
All17 post-domination cores do have generalized free triangles. The lexicographic
triangle-interval rule makes1438 verified reductions and then stalls on all17.
Do not confuse generalized free faces with codimension-one elementary pairs.
The failed stronger diagnostic and failed completion rule are preserved.

All prior flawed guesses remain recorded. Homology zero is not a collapse proof;
57 timeout and13 face-budget cases are not evidence of cancellation or failure.
The larger fixed-alphabet enumeration problem remains OPEN.

Local git metadata is stale: many untracked files are already remotely committed.
Do not reset or mass-add. Use the remote base tree plus precisely selected edits.
No merge to main, no claim of worldwide novelty.

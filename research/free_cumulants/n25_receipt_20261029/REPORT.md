# n=25 (j=5) all-five connected-kernel count: 6455

CI run 40942806037 (`five-pairs.yml`, commit `56d867d`, 128 shards)
completed: all 128 jobs `success`, retrieved as job-level check-run
annotations (`n25_counts.txt`, `n20_counts.txt` in this folder -- one line
per shard, `KERNEL_COUNT=` the per-shard partial count, as GitHub Actions
notice annotations rather than log files, since raw log download is
blocked from this project's sandbox).

## Validation before trusting the new number

- Confirmed all 128 shard indices `0..127` present exactly once for both
  `n=20` and `n=25` (no missing shard, no duplicate) by diffing the
  extracted shard-index list against `seq 0 127`.
- **n=20 (j=4) shard sum = 415** -- an exact match to the already-established
  value for j=4 (previously confirmed in this project, independent of this
  specific binary). This is the methodology's own self-check: the same
  `five_pairs` binary, same enumeration order, same "exactly two atoms,
  count the join once" certificate-pair definition
  (`research/free_cumulants/five_pairs.cpp`), computing a known answer
  correctly before trusting it on the new one.
- **n=25 (j=5) shard sum = 6455.** New value, not previously computed in
  this project (prior status: "n=25 (j=5) count still running").

Running sequence of all-five connected-kernel counts by number of
five-classes j: **j=2: 5, j=3: 35, j=4: 415, j=5: 6455**.

## What this is and isn't

This is the all-five connected kernel count only -- the number of
all-five-class, NC-connected patterns with exactly two noncrossing
pair/triple certificates whose join reconstructs the pattern (hence
`c(x) = -1` for each). It is VERIFIED-COMP from a single independently
sharded computation, cross-checked against the known j=2..4 values by the
same binary, but not yet independently reproduced by a second,
differently-written implementation at j=5 specifically. It is a term in
the free-cumulant expansion toward `connectedGameWeight`, not a value of
the original open fixed-q winning-word count `T(q,n)` itself, and not yet
a count that includes the mixed-block-size connected kernels the full
problem also needs (per `research/five_actual_20261029/REPORT.md`'s own
remaining-work list, item 4).

## Raw data

`n25_counts.txt`, `n20_counts.txt`: one `KERNEL_COUNT=...` notice message
per shard (128 lines each), pulled directly from
`gh api repos/.../check-runs/{job_id}/annotations` for every job in run
40942806037.

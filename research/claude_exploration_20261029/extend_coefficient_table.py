"""Open-ended computational exploration toward the fixed-q winning-word
count (the OEIS A035617-type open problem).

This does NOT reuse the NC-certificate/free-cumulant machinery the rest of
the project builds on. It re-derives the exact falling-factorial
coefficients c_k(n) of T(q,n) = sum_k c_k(n) * (q)_k directly from
`research/rgs_symbolic_count.py`'s restricted-growth-string DP over the
pair/triple grammar (an existing, independently-written ground truth in
this repo), purely as an outside check and a hunt for structure in the
coefficient sequences themselves -- closed forms, OEIS matches, generating
functions -- that the certificate-theoretic approach has not yet surfaced.

The DP's state space grows worse than exponentially in n (observed: n=15
already takes ~25s on 2 cores; n=16 did not finish in 100s locally), so
this script is deliberately time-budgeted: it computes as far as it can
within TIME_BUDGET_SECONDS and reports exactly how far it got, rather than
hanging a CI job. Every row is flushed to the output JSON immediately so a
timeout still leaves a maximal usable table.
"""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from research.rgs_symbolic_count import coefficient_counts  # noqa: E402

TIME_BUDGET_SECONDS = float(sys.argv[1]) if len(sys.argv) > 1 else 600.0
OUT_PATH = Path(__file__).parent / "coefficient_table.json"


def main():
    start = time.time()
    table = {}
    n = 1
    while True:
        elapsed = time.time() - start
        remaining = TIME_BUDGET_SECONDS - elapsed
        if remaining <= 1.0:
            print(f"time budget exhausted before n={n}; stopping", flush=True)
            break
        t0 = time.time()
        try:
            Q = n // 2
            coeffs, levels, cache_size = coefficient_counts(Q, n)
        except Exception as exc:  # pragma: no cover - diagnostic only
            print(f"n={n}: ERROR {exc!r}", flush=True)
            break
        dt = time.time() - t0
        table[n] = {"Q": Q, "coefficients": coeffs, "seconds": dt,
                    "max_state_level": max(levels) if levels else 0,
                    "cache_size": cache_size}
        print(f"n={n} Q={Q} coeffs={coeffs} ({dt:.2f}s, cache={cache_size})",
              flush=True)
        OUT_PATH.write_text(json.dumps(table, indent=2, sort_keys=True))
        if dt > remaining:
            print(f"n={n} took {dt:.1f}s, exceeding remaining budget "
                  f"{remaining:.1f}s; stopping before n={n+1}", flush=True)
            break
        n += 1
    print(f"done: computed n=1..{max(table)} in {time.time()-start:.1f}s"
          if table else "done: no rows computed", flush=True)
    return table


def columns(table):
    """Transpose to one sequence per k: c_k(n) for n=1,2,3,..."""
    by_k = {}
    for n_str, row in table.items():
        n = int(n_str) if isinstance(n_str, str) else n_str
        for k_str, c in row["coefficients"].items():
            k = int(k_str) if isinstance(k_str, str) else k_str
            by_k.setdefault(k, {})[n] = c
    return by_k


if __name__ == "__main__":
    tbl = main()
    cols = columns(tbl)
    print("\n--- per-k column sequences (for OEIS lookup) ---", flush=True)
    for k in sorted(cols):
        ns = sorted(cols[k])
        seq = [cols[k][n] for n in ns]
        print(f"k={k} (n={ns[0]}..{ns[-1]}): {seq}", flush=True)

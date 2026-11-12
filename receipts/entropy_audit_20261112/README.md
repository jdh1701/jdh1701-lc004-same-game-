# Fresh replay of the November 11 entropy certificate

This checkpoint imports the unchanged decisive certificate and paper report from the private LC004 evidence Site source commit `7b4bec75d715dedcf7fca3565f29102bdaa46f52` into a separate GitHub audit branch. It does not merge or overwrite prior research.

## Actually rerun

On the current cloud computer, Python 3.12.14:

- `audit_certificate.py prefix9-1.txt tilted10-9.certificate.txt`: PASS; 138,774 semantic transitions; 46,258 exact integer inequalities; worst drift numerator -3,041,932 over denominator 2,800,000,000.
- The Site's `reproduce.py --full`: PASS, including the regeneration failure certificate and 295,240 exhaustive prefix/window cases. Its log is preserved as `full-replay.txt`. That full replay requires the larger original Site archive, not just this minimal GitHub import.

The model, certificate and checker hashes agree with the preserved November 11 record. This is a new execution of existing checkers, not an independently implemented checker or external review. The supplied workflow replays the minimal decisive certificate on GitHub Actions; do not infer CI success from the workflow file's existence.

## Mathematical review scope

The report's lower bound uses a conservative subset of reachable stacks; that is sufficient for a lower bound, not exact recognition. Its base witness preserves the preceding prefix, so the two-letter representative lifting is plausible and explicit. The boundary repair and fixed-length suffix avoid reliance on a next-to-last color at small base height. The entropy calculation is under a history-dependent tilted input law, not uniform input. These distinctions must remain in any public claim.

No new Lean theorem, no independent novelty certification, and no solution of exact enumeration is claimed. The paper proof still needs independent mathematical review/formalization of the lifting, boundary, drift-to-tail and entropy-to-count implications. The imported REPORT.md is historical and retains its original statements that no GitHub change had occurred at that checkpoint; this dated addendum supersedes only that operational status, once this branch is verified on the remote.

The exact proposed lower bound remains `28/(10^10 * 9^18)^(1/28)`, displayed approximately as 2.9962190503368857. This replay validates its finite certificate premises, not the entire probability argument in a proof assistant.

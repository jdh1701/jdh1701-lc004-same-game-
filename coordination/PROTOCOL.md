# Working protocol: John, ChatGPT, Claude

This replaces the stacked-branch workflow of the old repository. In that repository, 30 PRs were stacked on top of each other and `main` fell a month behind the actual research. The rules from [`research/coordination/README.md`](../research/coordination/README.md) and the WORKBOARD protocol still apply. What changes is where work lands.

## 1. `main` is the truth

- `main` always holds the current state: Lean, research and the WORKBOARD.
- Work goes on a short branch, `<agent>/<topic>-<yyyymmdd>`, for example `gpt/first-excess-core-20261118`. The branch is cut from the current `main`, never from another open branch.
- Open a PR into `main`. **Merge as soon as CI is green and the change is reviewed or self-contained.** Do not start a second branch on top of an unmerged one. If you need its content, merge it first.
- A PR that touches `LC004/` merges only on a green `lean.yml` run on its exact head. That run includes the coverage check and the axiom audit.
- A PR that only adds documentation or research data can merge without Lean CI.

## 2. Where things go

| What | Where |
|---|---|
| A new Lean module | `LC004/`, imported from `LC004.lean`. The coverage check fails if it is not imported. |
| A new line of research | `research/<topic>_<yyyymmdd>/` with a `REPORT.md` (results and status words), a `HANDOFF.md` (exact next obligation) and its scripts, data and receipts |
| A new claim, change of status, kill or retraction | One row or line in [`research/WORKBOARD.md`](../research/WORKBOARD.md), in the same PR |
| A one-page summary | Update [`STATUS.md`](../STATUS.md) whenever the WORKBOARD changes status |
| Questions between models | [`coordination/OPEN_REQUESTS.md`](OPEN_REQUESTS.md), plus a dated file under `coordination/requests/` |
| A new research folder | Add a row to [`docs/RESEARCH_INDEX.md`](../docs/RESEARCH_INDEX.md) |

## 3. Handoffs between models

A commit does not mean the other model has seen it. Every request gets an ID, `R-yyyy-mm-dd[-x]`, and a file `coordination/requests/R-….md` containing:

- the source SHA it refers to
- the claim or obligation IDs it concerns
- the exact numbered questions
- what would count as an answer

The reply goes in the same file under `## Response`. The reply records:

- the reviewed SHA
- coverage per question: answered, partial or not addressed
- evidence and its test scope
- objections that remain unresolved
- the next owner

Then update the request's row in `OPEN_REQUESTS.md`. Partial replies say they are partial.

**John's short instruction to either model:** "Check OPEN_REQUESTS and answer what's addressed to you." This means:

1. Read the request file.
2. Verify against source and receipts.
3. Answer in that file.
4. Update the row.

## 4. Status words

Use exactly one of these per claim:

- **PROVED-LEAN**: in the build closure, with a green CI run on the cited commit and the axiom audit passing.
- **PROVED-PAPER**: a complete written proof that is not machine-checked.
- **VERIFIED-COMP**: an exact computation over a stated finite range, with its script.
- **CONJECTURE**: survived the falsification attempts made so far.
- **KILLED**: refuted, with the counterexample.
- **RETRACTED**: a claim that was made and then withdrawn.

Negative results are results. Record them with the same care as positive ones.

Floating-point output is for discovery only. It never supports a PROVED or VERIFIED status.

## 5. Provenance

Files carried over from the old repository are listed in [`docs/provenance.json`](../docs/provenance.json) with their original branch, commit and blob. `python3 scripts/check_provenance.py` confirms that each one is unchanged. Do not edit archived files in place. Copy one forward and note where it came from.

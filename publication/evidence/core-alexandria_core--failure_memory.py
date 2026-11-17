"""Persistent failure memory backed by a transactional SQLite journal."""

from __future__ import annotations

import json
import sqlite3
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import Any, Self

from .models import canonical_json, stable_id

_SCHEMA = """
CREATE TABLE IF NOT EXISTS failures (
    signature TEXT PRIMARY KEY,
    category TEXT NOT NULL,
    claim_id TEXT NOT NULL,
    summary TEXT NOT NULL,
    first_run_id TEXT NOT NULL,
    last_run_id TEXT NOT NULL,
    occurrences INTEGER NOT NULL CHECK (occurrences > 0),
    details_json TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS observations (
    signature TEXT NOT NULL,
    run_id TEXT NOT NULL,
    report_fingerprint TEXT NOT NULL,
    details_json TEXT NOT NULL,
    PRIMARY KEY (signature, run_id),
    FOREIGN KEY (signature) REFERENCES failures(signature)
);
"""


class FailureMemory:
    def __init__(self, path: Path | str) -> None:
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._connection = sqlite3.connect(self.path)
        self._connection.row_factory = sqlite3.Row
        self._connection.execute("PRAGMA foreign_keys = ON")
        self._connection.execute("PRAGMA journal_mode = WAL")
        self._connection.executescript(_SCHEMA)

    def close(self) -> None:
        self._connection.close()

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *args: object) -> None:
        self.close()

    def remember(self, report: Mapping[str, Any]) -> int:
        run_id = str(report.get("run_id", "")).strip()
        fingerprint = str(report.get("fingerprint", "")).strip()
        if not run_id or not fingerprint:
            raise ValueError("report requires run_id and fingerprint")
        observations = tuple(self._extract(report))
        inserted = 0
        with self._connection:
            for row in observations:
                signature = stable_id(
                    "failure", row["category"], row["claim_id"], row["summary"]
                )
                details_json = canonical_json(row["details"])
                existing = self._connection.execute(
                    "SELECT 1 FROM observations WHERE signature = ? AND run_id = ?",
                    (signature, run_id),
                ).fetchone()
                if existing is not None:
                    continue
                inserted += 1
                self._connection.execute(
                    """
                    INSERT INTO failures
                        (signature, category, claim_id, summary, first_run_id,
                         last_run_id, occurrences, details_json)
                    VALUES (?, ?, ?, ?, ?, ?, 1, ?)
                    ON CONFLICT(signature) DO UPDATE SET
                        last_run_id = excluded.last_run_id,
                        occurrences = failures.occurrences + 1,
                        details_json = excluded.details_json
                    """,
                    (
                        signature,
                        row["category"],
                        row["claim_id"],
                        row["summary"],
                        run_id,
                        run_id,
                        details_json,
                    ),
                )
                self._connection.execute(
                    """
                    INSERT INTO observations
                        (signature, run_id, report_fingerprint, details_json)
                    VALUES (?, ?, ?, ?)
                    """,
                    (signature, run_id, fingerprint, details_json),
                )
        return inserted

    def recurring(self, minimum_occurrences: int = 2) -> list[dict[str, Any]]:
        if minimum_occurrences < 1:
            raise ValueError("minimum_occurrences must be positive")
        rows = self._connection.execute(
            """
            SELECT signature, category, claim_id, summary, first_run_id,
                   last_run_id, occurrences, details_json
            FROM failures
            WHERE occurrences >= ?
            ORDER BY occurrences DESC, signature ASC
            """,
            (minimum_occurrences,),
        ).fetchall()
        return [
            {
                "signature": row["signature"],
                "category": row["category"],
                "claim_id": row["claim_id"],
                "summary": row["summary"],
                "first_run_id": row["first_run_id"],
                "last_run_id": row["last_run_id"],
                "occurrences": row["occurrences"],
                "details": json.loads(row["details_json"]),
            }
            for row in rows
        ]

    def count(self) -> int:
        return int(
            self._connection.execute("SELECT COUNT(*) FROM failures").fetchone()[0]
        )

    def _extract(self, report: Mapping[str, Any]) -> Iterable[dict[str, Any]]:
        for claim in report.get("claims", []):
            if isinstance(claim, Mapping) and claim.get("disposition") == "rejected":
                yield {
                    "category": "rejected_claim",
                    "claim_id": str(claim.get("id", "unknown")),
                    "summary": str(claim.get("text", "rejected claim")),
                    "details": {"assessment": claim.get("assessment", {})},
                }
        for attack in report.get("attacks", []):
            if isinstance(attack, Mapping):
                yield {
                    "category": f"attack:{attack.get('category', 'unknown')}",
                    "claim_id": str(attack.get("claim_id", "unknown")),
                    "summary": str(attack.get("challenge", "adversarial finding")),
                    "details": dict(attack),
                }
        for obligation in report.get("obligations", []):
            if (
                isinstance(obligation, Mapping)
                and obligation.get("status") == "unsatisfied"
            ):
                yield {
                    "category": f"obligation:{obligation.get('kind', 'unknown')}",
                    "claim_id": str(obligation.get("claim_id", "unknown")),
                    "summary": str(
                        obligation.get("description", "unsatisfied obligation")
                    ),
                    "details": dict(obligation),
                }

"""Deterministic, hash-chained verification receipts and report replay checks."""

from __future__ import annotations

import hashlib
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import Any

from .models import canonical_json, stable_id

RECEIPT_SCHEMA = "alexandria-receipt/1"
GENESIS_HASH = "sha256:" + ("0" * 64)


def digest_object(value: object) -> str:
    return "sha256:" + hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


@dataclass(frozen=True, slots=True)
class Receipt:
    sequence: int
    event: str
    payload: Mapping[str, Any]
    payload_digest: str
    previous_receipt_hash: str
    receipt_hash: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": RECEIPT_SCHEMA,
            "sequence": self.sequence,
            "event": self.event,
            "payload": dict(self.payload),
            "payload_digest": self.payload_digest,
            "previous_receipt_hash": self.previous_receipt_hash,
            "receipt_hash": self.receipt_hash,
        }


class ReceiptLedger:
    def __init__(self) -> None:
        self._rows: list[Receipt] = []

    def append(self, event: str, payload: Mapping[str, Any]) -> Receipt:
        sequence = len(self._rows) + 1
        previous = self._rows[-1].receipt_hash if self._rows else GENESIS_HASH
        payload_copy = dict(payload)
        payload_digest = digest_object(payload_copy)
        unsigned = {
            "schema_version": RECEIPT_SCHEMA,
            "sequence": sequence,
            "event": event,
            "payload": payload_copy,
            "payload_digest": payload_digest,
            "previous_receipt_hash": previous,
        }
        receipt = Receipt(
            sequence=sequence,
            event=event,
            payload=payload_copy,
            payload_digest=payload_digest,
            previous_receipt_hash=previous,
            receipt_hash=digest_object(unsigned),
        )
        self._rows.append(receipt)
        return receipt

    def to_list(self) -> list[dict[str, Any]]:
        return [row.to_dict() for row in self._rows]


def build_receipts(
    events: Iterable[Mapping[str, Any]], core_report: Mapping[str, Any]
) -> list[dict[str, Any]]:
    ledger = ReceiptLedger()
    for event in events:
        event_type = str(event.get("event", "event"))
        ledger.append(event_type, event)
    ledger.append(
        "report_core_finalized",
        {
            "core_digest": digest_object(core_report),
            "engine_version": core_report.get("engine_version"),
            "schema_version": core_report.get("schema_version"),
        },
    )
    return ledger.to_list()


def verify_receipts(rows: object) -> tuple[bool, tuple[str, ...]]:
    if not isinstance(rows, list) or not rows:
        return False, ("receipt ledger must be a non-empty list",)
    reasons: list[str] = []
    previous = GENESIS_HASH
    for expected_sequence, row in enumerate(rows, start=1):
        if not isinstance(row, Mapping):
            reasons.append(f"receipt {expected_sequence} is not an object")
            continue
        if row.get("schema_version") != RECEIPT_SCHEMA:
            reasons.append(f"receipt {expected_sequence} has an unknown schema")
        if row.get("sequence") != expected_sequence:
            reasons.append(f"receipt {expected_sequence} has a non-contiguous sequence")
        payload = row.get("payload")
        if not isinstance(payload, Mapping):
            reasons.append(f"receipt {expected_sequence} payload is not an object")
            payload = {}
        if row.get("payload_digest") != digest_object(payload):
            reasons.append(f"receipt {expected_sequence} payload digest mismatch")
        if row.get("previous_receipt_hash") != previous:
            reasons.append(f"receipt {expected_sequence} chain predecessor mismatch")
        unsigned = {
            "schema_version": row.get("schema_version"),
            "sequence": row.get("sequence"),
            "event": row.get("event"),
            "payload": dict(payload),
            "payload_digest": row.get("payload_digest"),
            "previous_receipt_hash": row.get("previous_receipt_hash"),
        }
        calculated = digest_object(unsigned)
        if row.get("receipt_hash") != calculated:
            reasons.append(f"receipt {expected_sequence} hash mismatch")
        previous = str(row.get("receipt_hash") or calculated)
    return not reasons, tuple(reasons)


def verify_report(report: object) -> tuple[bool, tuple[str, ...]]:
    if not isinstance(report, Mapping):
        return False, ("report must be an object",)
    reasons: list[str] = []
    rows = report.get("receipts")
    receipts_valid, receipt_reasons = verify_receipts(rows)
    if not receipts_valid:
        reasons.extend(receipt_reasons)

    unsigned = dict(report)
    supplied_fingerprint = unsigned.pop("fingerprint", None)
    supplied_run_id = unsigned.pop("run_id", None)
    expected_fingerprint = hashlib.sha256(
        canonical_json(unsigned).encode("utf-8")
    ).hexdigest()
    if supplied_fingerprint != expected_fingerprint:
        reasons.append("report fingerprint mismatch")
    if supplied_run_id != stable_id("run", expected_fingerprint):
        reasons.append("report run_id mismatch")

    core = dict(unsigned)
    core.pop("receipts", None)
    if isinstance(rows, list) and rows:
        final = rows[-1]
        payload = final.get("payload", {}) if isinstance(final, Mapping) else {}
        if final.get("event") != "report_core_finalized":
            reasons.append("final receipt is not report_core_finalized")
        if not isinstance(payload, Mapping) or payload.get(
            "core_digest"
        ) != digest_object(core):
            reasons.append("final receipt does not bind the report core")
    return not reasons, tuple(dict.fromkeys(reasons))

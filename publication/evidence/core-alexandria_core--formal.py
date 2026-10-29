"""Claim-bound formal-proof receipts and the fail-closed theorem gate."""

from __future__ import annotations

import hashlib
import re
from collections.abc import Mapping, Sequence
from typing import Any

from .models import Claim, Verdict, VerificationResult, canonical_json, stable_id

FORMAL_PROOF_SCHEMA = "alexandria-formal-proof/2"
FORMAL_PROOF_GATE = "formal_proof_gate"
_SHA256 = re.compile(r"^sha256:[0-9a-f]{64}$")
_RECEIPT_FIELDS = {
    "schema_version",
    "claim_digest",
    "proof_system",
    "toolchain",
    "declaration",
    "kernel_verified",
    "proof_bundle_sha256",
    "checker_sha256",
    "kernel_sha256",
    "auditor_sha256",
    "trusted_axioms",
    "unresolved_goals",
    "unresolved_assumptions",
}


def formal_claim_payload(claim: Claim) -> dict[str, Any]:
    """Return the exact claim semantics a formal proof receipt must bind."""

    payload: dict[str, Any] = {
        "id": claim.id,
        "text": claim.text,
        "kind": claim.kind.value,
        "predicate": claim.predicate,
        "dependencies": list(claim.dependencies),
        "conflicts": list(claim.conflicts),
        "tags": list(claim.tags),
        "falsifier": claim.falsifier,
        "acceptance_criteria": list(claim.acceptance_criteria),
        "formalization": (
            claim.formalization.to_dict() if claim.formalization is not None else None
        ),
    }
    # Older claims omitted these optional fields. Preserve their existing
    # bindings, but never allow an explicit scope/quantifier change to reuse
    # the same formal receipt.
    if claim.quantifier is not None:
        payload["quantifier"] = claim.quantifier
    if claim.domain is not None:
        payload["domain"] = claim.domain
    return payload


def formal_claim_digest(claim: Claim) -> str:
    """Hash the full claim semantics used by a formal verifier."""

    payload = canonical_json(formal_claim_payload(claim)).encode("utf-8")
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _receipt_from(result: VerificationResult) -> Mapping[str, Any] | None:
    direct = result.details.get("formal_proof")
    if isinstance(direct, Mapping):
        return direct
    tool_details = result.details.get("tool_details")
    if isinstance(tool_details, Mapping):
        nested = tool_details.get("formal_proof")
        if isinstance(nested, Mapping):
            return nested
    return None


def _checker_binding(result: VerificationResult) -> object:
    if "execution_bundle_digest" in result.details:
        return result.details["execution_bundle_digest"]
    if "executable_digest" in result.details:
        return result.details["executable_digest"]
    return result.details.get("checker_digest")


def validate_formal_proof_receipt(
    claim: Claim,
    result: VerificationResult,
) -> tuple[bool, tuple[str, ...], Mapping[str, Any] | None]:
    """Validate one receipt and bind it to the result's actual checker identity."""

    reasons: list[str] = []
    if result.verdict is not Verdict.PASS:
        reasons.append("the proof-producing verifier did not return pass")
    if result.blocking:
        reasons.append("the proof-producing verifier marked its result as blocking")
    if result.claim_id != claim.id:
        reasons.append("the verifier result targets a different claim")

    receipt = _receipt_from(result)
    if receipt is None:
        return False, (*reasons, "formal_proof receipt is missing"), None

    unknown = set(receipt) - _RECEIPT_FIELDS
    missing = _RECEIPT_FIELDS - set(receipt)
    if missing:
        reasons.append(f"receipt fields are missing: {sorted(missing)}")
    if unknown:
        reasons.append(f"receipt fields are unsupported: {sorted(unknown)}")
    if receipt.get("schema_version") != FORMAL_PROOF_SCHEMA:
        reasons.append(f"schema_version must be {FORMAL_PROOF_SCHEMA}")
    if receipt.get("claim_digest") != formal_claim_digest(claim):
        reasons.append("claim_digest does not bind the exact claim semantics")
    if (
        not isinstance(receipt.get("proof_system"), str)
        or not str(receipt.get("proof_system", "")).strip()
    ):
        reasons.append("proof_system must be a non-empty string")
    if (
        not isinstance(receipt.get("toolchain"), str)
        or not str(receipt.get("toolchain", "")).strip()
    ):
        reasons.append("toolchain must be a non-empty string")
    if (
        not isinstance(receipt.get("declaration"), str)
        or not str(receipt.get("declaration", "")).strip()
    ):
        reasons.append("declaration must be a non-empty string")
    if receipt.get("kernel_verified") is not True:
        reasons.append("kernel_verified must be true")

    for field in (
        "proof_bundle_sha256",
        "checker_sha256",
        "kernel_sha256",
        "auditor_sha256",
    ):
        value = receipt.get(field)
        if not isinstance(value, str) or not _SHA256.fullmatch(value):
            reasons.append(f"{field} must use sha256:<64 lowercase hex characters>")

    goals = receipt.get("unresolved_goals")
    if isinstance(goals, bool) or not isinstance(goals, int) or goals != 0:
        reasons.append("unresolved_goals must be the integer 0")
    assumptions = receipt.get("unresolved_assumptions")
    if not isinstance(assumptions, list) or assumptions:
        reasons.append("unresolved_assumptions must be an empty list")
    trusted_axioms = receipt.get("trusted_axioms")
    if not isinstance(trusted_axioms, list) or not all(
        isinstance(value, str) and value.strip() for value in trusted_axioms
    ):
        reasons.append("trusted_axioms must be a string list")
    elif trusted_axioms != sorted(set(trusted_axioms)):
        reasons.append("trusted_axioms must be sorted and unique")

    formalization = claim.formalization
    if formalization is None:
        reasons.append("claim has no operator-pinned formalization")
    else:
        if receipt.get("proof_system") != formalization.system:
            reasons.append("proof_system does not match the claim formalization")
        if receipt.get("declaration") != formalization.declaration:
            reasons.append("declaration does not match the claim formalization")
        if receipt.get("proof_bundle_sha256") != formalization.proof_bundle_sha256:
            reasons.append("proof_bundle_sha256 does not match the claim formalization")

    checker = _checker_binding(result)
    if checker != receipt.get("checker_sha256"):
        reasons.append("checker_sha256 does not match the executing trusted checker")
    return not reasons, tuple(dict.fromkeys(reasons)), receipt


def formal_proof_gate(
    claim: Claim,
    results: Sequence[VerificationResult],
    trusted_authorities: frozenset[str],
) -> VerificationResult:
    """Require a valid receipt from an explicitly trusted formal authority."""

    candidates = [
        result
        for result in results
        if result.verifier in trusted_authorities
        and result.verifier != FORMAL_PROOF_GATE
    ]
    failures: list[dict[str, Any]] = []
    for result in candidates:
        valid, reasons, receipt = validate_formal_proof_receipt(claim, result)
        if valid and receipt is not None:
            receipt_digest = (
                "sha256:"
                + hashlib.sha256(canonical_json(receipt).encode("utf-8")).hexdigest()
            )
            details = {
                "authority": result.verifier,
                "claim_digest": receipt["claim_digest"],
                "proof_system": receipt["proof_system"],
                "toolchain": receipt["toolchain"],
                "declaration": receipt["declaration"],
                "proof_bundle_sha256": receipt["proof_bundle_sha256"],
                "checker_sha256": receipt["checker_sha256"],
                "kernel_sha256": receipt["kernel_sha256"],
                "auditor_sha256": receipt["auditor_sha256"],
                "trusted_axioms": receipt["trusted_axioms"],
                "receipt_digest": receipt_digest,
                "source_verification_id": result.id,
            }
            message = f"claim-bound kernel proof verified by trusted authority {result.verifier}"
            return VerificationResult(
                id=stable_id(
                    "verification", claim.id, FORMAL_PROOF_GATE, "pass", details
                ),
                claim_id=claim.id,
                verifier=FORMAL_PROOF_GATE,
                verdict=Verdict.PASS,
                message=message,
                details=details,
                blocking=False,
            )
        failures.append({"verifier": result.verifier, "reasons": list(reasons)})

    if not candidates:
        message = "no explicitly trusted formal verifier supplied a proof receipt"
    else:
        message = (
            "no trusted formal verifier supplied a valid claim-bound proof receipt"
        )
    details = {
        "expected_claim_digest": formal_claim_digest(claim),
        "trusted_authorities": sorted(trusted_authorities),
        "candidate_failures": failures,
    }
    return VerificationResult(
        id=stable_id("verification", claim.id, FORMAL_PROOF_GATE, "fail", details),
        claim_id=claim.id,
        verifier=FORMAL_PROOF_GATE,
        verdict=Verdict.FAIL,
        message=message,
        details=details,
        blocking=True,
    )


def proof_status(results: Sequence[VerificationResult]) -> str:
    gates = [result for result in results if result.verifier == FORMAL_PROOF_GATE]
    return (
        "verified"
        if len(gates) == 1
        and gates[0].verdict is Verdict.PASS
        and not gates[0].blocking
        else "missing_or_invalid"
    )

"""Constrained subprocess contract for Lean, Z3, and domain verifier adapters."""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import signal

# This module is the deliberate constrained subprocess boundary.
import subprocess  # nosec B404
import sys
import tempfile
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .control import ControlPolicy
from .formal import formal_claim_digest
from .models import (
    Claim,
    ClaimKind,
    Evidence,
    ValidationError,
    Verdict,
    VerificationResult,
    stable_id,
)

_NAME = re.compile(r"^[A-Za-z0-9_.-]+$")
VERIFIER_REGISTRY_SCHEMA = "alexandria-verifier-registry/1"
_REGISTRY_FIELDS = {"schema_version", "verifiers"}
_VERIFIER_FIELDS = {
    "name",
    "executable",
    "arguments",
    "claim_kinds",
    "required_tag",
    "timeout_seconds",
    "max_output_bytes",
    "max_memory_mb",
    "executable_sha256",
    "execution_bundle_sha256",
    "isolation",
    "formal_proof_authority",
}


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


@dataclass(frozen=True, slots=True)
class ExternalVerifierSpec:
    name: str
    executable: Path
    arguments: tuple[str, ...] = ()
    claim_kinds: tuple[ClaimKind, ...] = tuple(ClaimKind)
    required_tag: str | None = None
    timeout_seconds: float = 10.0
    max_output_bytes: int = 1_000_000
    max_memory_mb: int = 512
    executable_sha256: str | None = None
    execution_bundle_sha256: str | None = None
    isolation: str = "process"

    def __post_init__(self) -> None:
        if not _NAME.fullmatch(self.name):
            raise ValueError("external verifier name contains unsupported characters")
        if not self.executable.is_absolute():
            raise ValueError("external verifier executable must be an absolute path")
        if not self.executable.is_file():
            raise ValueError(
                f"external verifier executable does not exist: {self.executable}"
            )
        if not 0.1 <= self.timeout_seconds <= 120.0:
            raise ValueError("timeout_seconds must be between 0.1 and 120")
        if not 1_024 <= self.max_output_bytes <= 10_000_000:
            raise ValueError("max_output_bytes must be between 1 KiB and 10 MB")
        if not 64 <= self.max_memory_mb <= 8_192:
            raise ValueError("max_memory_mb must be between 64 and 8192")
        if self.isolation not in {"process", "container"}:
            raise ValueError("isolation must be process or container")
        if self.executable_sha256 is not None and not re.fullmatch(
            r"sha256:[0-9a-f]{64}", self.executable_sha256
        ):
            raise ValueError(
                "executable_sha256 must use sha256:<64 lowercase hex characters>"
            )
        if self.execution_bundle_sha256 is not None and not re.fullmatch(
            r"sha256:[0-9a-f]{64}", self.execution_bundle_sha256
        ):
            raise ValueError(
                "execution_bundle_sha256 must use sha256:<64 lowercase hex characters>"
            )


def execution_bundle_digest(spec: ExternalVerifierSpec) -> str:
    """Bind the executable, every literal argument, and all absolute file arguments."""

    arguments: list[dict[str, str]] = []
    for value in spec.arguments:
        row = {"value": value}
        path = Path(value)
        if path.is_absolute() and path.is_file():
            row["file_sha256"] = _file_sha256(path)
        arguments.append(row)
    payload = {
        "schema_version": "alexandria-checker-bundle/1",
        "executable": str(spec.executable),
        "executable_sha256": _file_sha256(spec.executable),
        "arguments": arguments,
    }
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _request(
    claim: Claim,
    evidence: tuple[Evidence, ...],
    policy: ControlPolicy,
    *,
    verifier_name: str,
    checker_digest: str,
) -> bytes:
    payload = {
        "schema_version": "alexandria-verifier-request/1",
        "claim": {
            "id": claim.id,
            "text": claim.text,
            "kind": claim.kind.value,
            "predicate": claim.predicate,
            "falsifier": claim.falsifier,
            "acceptance_criteria": list(claim.acceptance_criteria),
            "dependencies": list(claim.dependencies),
            "conflicts": list(claim.conflicts),
            "tags": list(claim.tags),
            "formal_claim_digest": formal_claim_digest(claim),
            "formalization": (
                claim.formalization.to_dict()
                if claim.formalization is not None
                else None
            ),
        },
        "evidence": [
            {
                "id": item.id,
                "direction": item.direction.value,
                "description": item.description,
                "source": item.source,
                "source_type": item.source_type,
                "content_hash": item.content_hash,
                "strength": item.strength,
                "reliability": item.reliability,
                "independence_group": item.independence_group,
            }
            for item in evidence
        ],
        "policy": {
            "mode": policy.mode.value,
            "fail_closed_on_verifier_error": policy.fail_closed_on_verifier_error,
        },
        "verifier": {
            "name": verifier_name,
            "checker_sha256": checker_digest,
        },
    }
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )


def _command(spec: ExternalVerifierSpec) -> list[str]:
    target = [str(spec.executable), *spec.arguments]
    if os.name != "posix":
        return target
    launcher = Path(__file__).with_name("_verifier_launcher.py")
    return [
        str(Path(sys.executable).resolve()),
        "-I",
        "-S",
        str(launcher),
        str(max(1, math.ceil(spec.timeout_seconds) + 1)),
        str(spec.max_memory_mb * 1024 * 1024),
        str(spec.max_output_bytes),
        *target,
    ]


class SubprocessVerifier:
    """Invoke a fixed executable with bounded resources and a strict JSON contract.

    Process isolation limits resources but does not block network syscalls. War mode therefore
    requires a caller-supplied container wrapper and a pinned executable digest.
    """

    def __init__(self, spec: ExternalVerifierSpec) -> None:
        self.spec = spec
        self.name = spec.name

    def applies(self, claim: Claim) -> bool:
        return claim.kind in self.spec.claim_kinds and (
            self.spec.required_tag is None or self.spec.required_tag in claim.tags
        )

    def verify(
        self, claim: Claim, evidence: tuple[Evidence, ...], policy: ControlPolicy
    ) -> VerificationResult:
        executable_digest = _file_sha256(self.spec.executable)
        checker_digest = execution_bundle_digest(self.spec)
        if (
            self.spec.executable_sha256
            and executable_digest != self.spec.executable_sha256
        ):
            return self._error(
                claim.id,
                "configured executable digest does not match the verifier binary",
                policy,
                executable_digest,
                checker_digest,
            )
        if (
            self.spec.execution_bundle_sha256
            and checker_digest != self.spec.execution_bundle_sha256
        ):
            return self._error(
                claim.id,
                "configured checker-bundle digest does not match the execution bundle",
                policy,
                executable_digest,
                checker_digest,
            )
        if policy.mode.value == "war" and (
            self.spec.isolation != "container" or not self.spec.executable_sha256
        ):
            return self._error(
                claim.id,
                "war mode requires container isolation and a pinned executable digest",
                policy,
                executable_digest,
                checker_digest,
            )

        request = _request(
            claim,
            evidence,
            policy,
            verifier_name=self.name,
            checker_digest=checker_digest,
        )
        with tempfile.TemporaryDirectory(prefix="alexandria-verifier-") as directory:
            root = Path(directory)
            stdout_path = root / "stdout.json"
            stderr_path = root / "stderr.log"
            process: subprocess.Popen[bytes] | None = None
            try:
                with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                    process = subprocess.Popen(
                        _command(self.spec),
                        stdin=subprocess.PIPE,
                        stdout=stdout,
                        stderr=stderr,
                        cwd=root,
                        env={
                            "LANG": "C.UTF-8",
                            "LC_ALL": "C.UTF-8",
                            "PYTHONHASHSEED": "0",
                        },
                        # The command is fixed by operator-trusted configuration.
                        shell=False,  # nosec B603
                        start_new_session=True,
                    )
                    process.communicate(
                        input=request, timeout=self.spec.timeout_seconds
                    )
            except subprocess.TimeoutExpired:
                if process is not None:
                    try:
                        if os.name == "posix":
                            os.killpg(process.pid, signal.SIGKILL)
                        else:
                            process.kill()
                    except ProcessLookupError:
                        pass
                    process.wait()
                return self._error(
                    claim.id,
                    f"verifier exceeded {self.spec.timeout_seconds:g}s timeout",
                    policy,
                    executable_digest,
                    checker_digest,
                )
            except OSError as error:
                return self._error(
                    claim.id,
                    f"verifier launch failed: {type(error).__name__}: {error}",
                    policy,
                    executable_digest,
                    checker_digest,
                )

            stdout_bytes = stdout_path.read_bytes()
            stderr_bytes = stderr_path.read_bytes()
            if len(stdout_bytes) > self.spec.max_output_bytes:
                return self._error(
                    claim.id,
                    "verifier output exceeded the configured byte limit",
                    policy,
                    executable_digest,
                    checker_digest,
                )
            if process is None or process.returncode != 0:
                return self._error(
                    claim.id,
                    f"verifier exited with status {process.returncode if process else 'unknown'}",
                    policy,
                    executable_digest,
                    checker_digest,
                    stderr_digest="sha256:" + hashlib.sha256(stderr_bytes).hexdigest(),
                )

        try:
            response = json.loads(stdout_bytes.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            return self._error(
                claim.id,
                f"verifier returned invalid UTF-8 JSON: {type(error).__name__}",
                policy,
                executable_digest,
                checker_digest,
            )
        if not isinstance(response, dict):
            return self._error(
                claim.id,
                "verifier response must be a JSON object",
                policy,
                executable_digest,
                checker_digest,
            )
        try:
            verdict = Verdict(str(response.get("verdict", "")).lower())
        except ValueError:
            return self._error(
                claim.id,
                "verifier response has an unknown verdict",
                policy,
                executable_digest,
                checker_digest,
            )
        message = response.get("message")
        details = response.get("details", {})
        if (
            not isinstance(message, str)
            or not message.strip()
            or not isinstance(details, dict)
        ):
            return self._error(
                claim.id,
                "verifier response requires a message string and details object",
                policy,
                executable_digest,
                checker_digest,
            )
        blocking = verdict in {Verdict.FAIL, Verdict.ERROR} or bool(
            response.get("blocking", False)
        )
        result_details: dict[str, Any] = {
            "tool_details": details,
            "executable_digest": executable_digest,
            "execution_bundle_digest": checker_digest,
            "isolation": self.spec.isolation,
            "response_digest": "sha256:" + hashlib.sha256(stdout_bytes).hexdigest(),
        }
        return VerificationResult(
            id=stable_id(
                "verification",
                claim.id,
                self.name,
                verdict.value,
                message,
                result_details,
            ),
            claim_id=claim.id,
            verifier=self.name,
            verdict=verdict,
            message=message.strip(),
            details=result_details,
            blocking=blocking,
        )

    def _error(
        self,
        claim_id: str,
        message: str,
        policy: ControlPolicy,
        executable_digest: str,
        checker_digest: str,
        *,
        stderr_digest: str | None = None,
    ) -> VerificationResult:
        details = {
            "executable_digest": executable_digest,
            "execution_bundle_digest": checker_digest,
            "isolation": self.spec.isolation,
            "stderr_digest": stderr_digest,
        }
        return VerificationResult(
            id=stable_id(
                "verification", claim_id, self.name, "error", message, details
            ),
            claim_id=claim_id,
            verifier=self.name,
            verdict=Verdict.ERROR,
            message=message,
            details=details,
            blocking=policy.fail_closed_on_verifier_error,
        )


def external_verifiers_from_mapping(
    raw: Mapping[str, Any],
) -> tuple[tuple[SubprocessVerifier, bool], ...]:
    """Build operator-trusted external verifiers from a strict registry document."""

    if set(raw) - _REGISTRY_FIELDS:
        raise ValidationError(
            f"verifier registry has unsupported fields: {sorted(set(raw) - _REGISTRY_FIELDS)}"
        )
    if raw.get("schema_version") != VERIFIER_REGISTRY_SCHEMA:
        raise ValidationError(
            f"verifier registry schema_version must be {VERIFIER_REGISTRY_SCHEMA}"
        )
    rows = raw.get("verifiers")
    if not isinstance(rows, list) or not rows:
        raise ValidationError("verifier registry requires a non-empty verifiers list")

    registered: list[tuple[SubprocessVerifier, bool]] = []
    names: set[str] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            raise ValidationError(f"verifier registry row {index} must be an object")
        unknown = set(row) - _VERIFIER_FIELDS
        if unknown:
            raise ValidationError(
                f"verifier registry row {index} has unsupported fields: {sorted(unknown)}"
            )
        name = row.get("name")
        executable = row.get("executable")
        arguments = row.get("arguments", [])
        claim_kinds = row.get("claim_kinds", [kind.value for kind in ClaimKind])
        authority = row.get("formal_proof_authority", False)
        if not isinstance(name, str) or not name.strip():
            raise ValidationError(
                f"verifier registry row {index}.name must be non-empty"
            )
        if name in names:
            raise ValidationError(f"verifier registry repeats verifier name {name}")
        if not isinstance(executable, str) or not executable.strip():
            raise ValidationError(
                f"verifier registry row {index}.executable must be non-empty"
            )
        if not isinstance(arguments, list) or not all(
            isinstance(value, str) for value in arguments
        ):
            raise ValidationError(
                f"verifier registry row {index}.arguments must be a string list"
            )
        if (
            not isinstance(claim_kinds, list)
            or not claim_kinds
            or not all(isinstance(value, str) for value in claim_kinds)
        ):
            raise ValidationError(
                f"verifier registry row {index}.claim_kinds must be a non-empty string list"
            )
        if not isinstance(authority, bool):
            raise ValidationError(
                f"verifier registry row {index}.formal_proof_authority must be boolean"
            )
        required_tag = row.get("required_tag")
        if required_tag is not None and (
            not isinstance(required_tag, str) or not required_tag.strip()
        ):
            raise ValidationError(
                f"verifier registry row {index}.required_tag must be non-empty when supplied"
            )
        try:
            kinds = tuple(ClaimKind(value.lower()) for value in claim_kinds)
            spec = ExternalVerifierSpec(
                name=name,
                executable=Path(executable),
                arguments=tuple(arguments),
                claim_kinds=kinds,
                required_tag=required_tag,
                timeout_seconds=_registry_float(row, "timeout_seconds", 10.0, index),
                max_output_bytes=_registry_int(
                    row, "max_output_bytes", 1_000_000, index
                ),
                max_memory_mb=_registry_int(row, "max_memory_mb", 512, index),
                executable_sha256=_registry_optional_string(
                    row, "executable_sha256", index
                ),
                execution_bundle_sha256=_registry_optional_string(
                    row, "execution_bundle_sha256", index
                ),
                isolation=_registry_string(row, "isolation", "process", index),
            )
        except ValueError as error:
            raise ValidationError(
                f"invalid verifier registry row {index}: {error}"
            ) from error
        if authority and spec.execution_bundle_sha256 is None:
            raise ValidationError(
                f"verifier registry row {index}.execution_bundle_sha256 is required "
                "for a formal proof authority"
            )
        names.add(name)
        registered.append((SubprocessVerifier(spec), authority))
    return tuple(registered)


def _registry_float(
    row: Mapping[str, Any], field: str, default: float, index: int
) -> float:
    value = row.get(field, default)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValidationError(f"verifier registry row {index}.{field} must be numeric")
    return float(value)


def _registry_int(row: Mapping[str, Any], field: str, default: int, index: int) -> int:
    value = row.get(field, default)
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValidationError(
            f"verifier registry row {index}.{field} must be an integer"
        )
    return value


def _registry_optional_string(
    row: Mapping[str, Any], field: str, index: int
) -> str | None:
    value = row.get(field)
    if value is not None and not isinstance(value, str):
        raise ValidationError(f"verifier registry row {index}.{field} must be a string")
    return value


def _registry_string(
    row: Mapping[str, Any], field: str, default: str, index: int
) -> str:
    value = row.get(field, default)
    if not isinstance(value, str):
        raise ValidationError(f"verifier registry row {index}.{field} must be a string")
    return value

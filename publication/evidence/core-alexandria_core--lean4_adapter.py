"""Replay a manifest-pinned Lean 4 proof bundle and emit an Alexandria receipt.

This file is deliberately standard-library-only so an operator can execute it as a fixed,
content-addressed external checker through :mod:`alexandria_core.external`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil

# This module is a fixed operator-controlled checker boundary.
import subprocess  # nosec B404
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any

BUNDLE_SCHEMA = "alexandria-lean4-bundle/1"
RECEIPT_SCHEMA = "alexandria-formal-proof/2"
_SHA256 = re.compile(r"^sha256:[0-9a-f]{64}$")
_LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
_BUNDLE_FIELDS = {
    "schema_version",
    "proof_system",
    "toolchain",
    "build_target",
    "module",
    "declaration",
    "allowed_axioms",
    "sources",
}


class AdapterError(ValueError):
    """A fail-closed configuration, bundle, replay, or audit error."""


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _sha256_bytes(value: bytes) -> str:
    return "sha256:" + hashlib.sha256(value).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def proof_bundle_digest(raw: Mapping[str, Any]) -> str:
    """Return the canonical semantic digest of a proof-bundle manifest."""

    return _sha256_bytes(_canonical_json(raw).encode("utf-8"))


def _load_object(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise AdapterError(
            f"cannot read {label}: {type(error).__name__}: {error}"
        ) from error
    except json.JSONDecodeError as error:
        raise AdapterError(f"invalid JSON in {label}: {error}") from error
    if not isinstance(value, dict):
        raise AdapterError(f"{label} must contain a JSON object")
    return value


def _nonempty_string(raw: Mapping[str, Any], field: str) -> str:
    value = raw.get(field)
    if not isinstance(value, str) or not value.strip():
        raise AdapterError(f"proof bundle {field} must be a non-empty string")
    return value.strip()


def _source_path(value: object) -> PurePosixPath:
    if not isinstance(value, str) or not value:
        raise AdapterError("proof bundle source.path must be a non-empty string")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "." in path.parts:
        raise AdapterError("proof bundle source paths must be normalized and relative")
    return path


def _tracked_files(root: Path, *, include_lake_manifest: bool) -> set[str]:
    tracked: set[str] = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root)
        if not path.is_file() or ".lake" in relative.parts or ".git" in relative.parts:
            continue
        name = relative.as_posix()
        if name == "alexandria-proof.json":
            continue
        if name == "lake-manifest.json" and not include_lake_manifest:
            continue
        tracked.add(name)
    return tracked


def validate_bundle(raw: Mapping[str, Any], root: Path) -> dict[str, Any]:
    """Strictly validate a manifest and every source digest before execution."""

    unknown = set(raw) - _BUNDLE_FIELDS
    missing = _BUNDLE_FIELDS - set(raw)
    if unknown:
        raise AdapterError(f"proof bundle has unsupported fields: {sorted(unknown)}")
    if missing:
        raise AdapterError(f"proof bundle fields are missing: {sorted(missing)}")
    if raw.get("schema_version") != BUNDLE_SCHEMA:
        raise AdapterError(f"proof bundle schema_version must be {BUNDLE_SCHEMA}")
    if raw.get("proof_system") != "lean4":
        raise AdapterError("proof bundle proof_system must be lean4")

    toolchain = _nonempty_string(raw, "toolchain")
    build_target = _nonempty_string(raw, "build_target")
    module = _nonempty_string(raw, "module")
    declaration = _nonempty_string(raw, "declaration")
    for label, value in (("module", module), ("declaration", declaration)):
        if not _LEAN_NAME.fullmatch(value):
            raise AdapterError(f"proof bundle {label} is not a supported Lean name")

    allowed_axioms = raw.get("allowed_axioms")
    if not isinstance(allowed_axioms, list) or not all(
        isinstance(value, str) and _LEAN_NAME.fullmatch(value)
        for value in allowed_axioms
    ):
        raise AdapterError("proof bundle allowed_axioms must be a Lean-name list")
    if allowed_axioms != sorted(set(allowed_axioms)):
        raise AdapterError("proof bundle allowed_axioms must be sorted and unique")

    source_rows = raw.get("sources")
    if not isinstance(source_rows, list) or not source_rows:
        raise AdapterError("proof bundle sources must be a non-empty list")
    source_paths: list[str] = []
    normalized_rows: list[dict[str, str]] = []
    for index, row in enumerate(source_rows):
        if not isinstance(row, Mapping) or set(row) != {"path", "sha256"}:
            raise AdapterError(
                f"proof bundle source {index} requires exactly path and sha256"
            )
        relative = _source_path(row.get("path"))
        digest = row.get("sha256")
        if not isinstance(digest, str) or not _SHA256.fullmatch(digest):
            raise AdapterError(
                f"proof bundle source {index}.sha256 is not canonical SHA-256"
            )
        path = root.joinpath(*relative.parts)
        if not path.is_file():
            raise AdapterError(f"proof bundle source is missing: {relative.as_posix()}")
        if _sha256_file(path) != digest:
            raise AdapterError(
                f"proof bundle source digest mismatch: {relative.as_posix()}"
            )
        source_paths.append(relative.as_posix())
        normalized_rows.append({"path": relative.as_posix(), "sha256": digest})
    if source_paths != sorted(set(source_paths)):
        raise AdapterError("proof bundle source paths must be sorted and unique")

    lakefile = root / "lakefile.toml"
    if not lakefile.is_file():
        lakefile = root / "lakefile.lean"
    if not lakefile.is_file():
        raise AdapterError("proof bundle requires lakefile.toml or lakefile.lean")
    lake_text = lakefile.read_text(encoding="utf-8")
    has_dependencies = "[[require]]" in lake_text or re.search(
        r"(?m)^\s*require\s+", lake_text
    )
    if has_dependencies and "lake-manifest.json" not in source_paths:
        raise AdapterError(
            "proof bundles with dependencies must pin lake-manifest.json"
        )
    tracked = _tracked_files(
        root, include_lake_manifest="lake-manifest.json" in source_paths
    )
    if set(source_paths) != tracked:
        missing_sources = sorted(tracked - set(source_paths))
        extra_sources = sorted(set(source_paths) - tracked)
        raise AdapterError(
            "proof bundle source inventory mismatch: "
            f"unlisted={missing_sources}, unsupported={extra_sources}"
        )

    toolchain_path = root / "lean-toolchain"
    if not toolchain_path.is_file():
        raise AdapterError("proof bundle must include lean-toolchain")
    if toolchain_path.read_text(encoding="utf-8").strip() != toolchain:
        raise AdapterError("proof bundle toolchain does not match lean-toolchain")
    return {
        "toolchain": toolchain,
        "build_target": build_target,
        "module": module,
        "declaration": declaration,
        "allowed_axioms": allowed_axioms,
        "sources": normalized_rows,
    }


def _run(command: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    try:
        executable_directory = str(Path(command[0]).parent)
        # The executable paths are fixed operator arguments, never scenario data.
        return subprocess.run(  # nosec B603
            list(command),
            cwd=cwd,
            env={
                "HOME": str(cwd),
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "LEAN_NUM_THREADS": "0",
                "PATH": os.pathsep.join((executable_directory, "/usr/bin", "/bin")),
            },
            text=True,
            capture_output=True,
            check=False,
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AdapterError(
            f"checker process failed: {type(error).__name__}: {error}"
        ) from error


def _output_digest(process: subprocess.CompletedProcess[str]) -> str:
    return _sha256_bytes((process.stdout + "\n" + process.stderr).encode("utf-8"))


def _response(verdict: str, message: str, details: Mapping[str, Any]) -> int:
    print(
        _canonical_json(
            {"verdict": verdict, "message": message, "details": dict(details)}
        )
    )
    return 0


def _check_request(raw: Mapping[str, Any]) -> tuple[dict[str, Any], str]:
    if raw.get("schema_version") != "alexandria-verifier-request/1":
        raise AdapterError("unsupported verifier request schema")
    claim = raw.get("claim")
    verifier = raw.get("verifier")
    if not isinstance(claim, dict) or not isinstance(verifier, dict):
        raise AdapterError("verifier request requires claim and verifier objects")
    if claim.get("kind") != "theorem":
        raise AdapterError("Lean adapter only accepts theorem claims")
    claim_digest = claim.get("formal_claim_digest")
    checker_digest = verifier.get("checker_sha256")
    if not isinstance(claim_digest, str) or not _SHA256.fullmatch(claim_digest):
        raise AdapterError("request formal_claim_digest is invalid")
    if not isinstance(checker_digest, str) or not _SHA256.fullmatch(checker_digest):
        raise AdapterError("request checker_sha256 is invalid")
    formalization = claim.get("formalization")
    if not isinstance(formalization, dict):
        raise AdapterError("the theorem has no pinned formalization")
    return formalization, checker_digest


def replay(
    request: Mapping[str, Any],
    *,
    bundle_path: Path,
    lake: Path,
    lean: Path,
    auditor: Path,
) -> tuple[str, str, dict[str, Any]]:
    """Replay one request, returning response verdict, message, and details."""

    formalization, checker_digest = _check_request(request)
    for label, path in (
        ("bundle", bundle_path),
        ("lake", lake),
        ("lean", lean),
        ("auditor", auditor),
    ):
        if not path.is_absolute() or not path.is_file():
            raise AdapterError(f"{label} path must be an existing absolute file")

    bundle_raw = _load_object(bundle_path, "proof bundle")
    bundle = validate_bundle(bundle_raw, bundle_path.parent)
    bundle_digest = proof_bundle_digest(bundle_raw)
    expected = {
        "system": "lean4",
        "declaration": bundle["declaration"],
        "proof_bundle_sha256": bundle_digest,
    }
    if formalization != expected:
        raise AdapterError("request formalization does not match the proof bundle")

    version = _run((str(lean), "--version"), cwd=bundle_path.parent)
    if version.returncode != 0:
        raise AdapterError(
            "Lean version check failed "
            f"with status {version.returncode} and output {_output_digest(version)}"
        )
    release = bundle["toolchain"].rsplit(":v", 1)[-1]
    if f"version {release}" not in version.stdout:
        raise AdapterError("Lean binary version does not match the pinned toolchain")

    with tempfile.TemporaryDirectory(prefix="alexandria-lean4-") as directory:
        replay_root = Path(directory) / "proof"
        replay_root.mkdir()
        for row in bundle["sources"]:
            source = bundle_path.parent / row["path"]
            destination = replay_root / row["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        build = _run((str(lake), "build", str(bundle["build_target"])), cwd=replay_root)
        if build.returncode != 0:
            return (
                "fail",
                "Lean rejected the proof bundle",
                {
                    "build_output_sha256": _output_digest(build),
                    "proof_bundle_sha256": bundle_digest,
                },
            )
        allowed = ",".join(bundle["allowed_axioms"])
        audit = _run(
            (
                str(lake),
                "env",
                str(auditor),
                "--module",
                str(bundle["module"]),
                "--declaration",
                str(bundle["declaration"]),
                "--allow",
                allowed,
            ),
            cwd=replay_root,
        )
        try:
            audit_raw = json.loads(audit.stdout)
        except json.JSONDecodeError as error:
            raise AdapterError("Lean auditor returned invalid JSON") from error
        if not isinstance(audit_raw, dict):
            raise AdapterError("Lean auditor response must be an object")
        axioms = audit_raw.get("axioms")
        unresolved = audit_raw.get("unresolved_assumptions")
        if (
            not isinstance(axioms, list)
            or not all(isinstance(value, str) for value in axioms)
            or axioms != sorted(set(axioms))
            or not isinstance(unresolved, list)
            or not all(isinstance(value, str) for value in unresolved)
            or unresolved != sorted(set(unresolved))
        ):
            raise AdapterError("Lean auditor returned malformed axiom lists")
        if (
            audit.returncode != 0
            or audit_raw.get("ok") is not True
            or audit_raw.get("declaration") != bundle["declaration"]
            or unresolved
        ):
            return (
                "fail",
                "Lean proof depends on unresolved or disallowed assumptions",
                {
                    "audit_output_sha256": _output_digest(audit),
                    "proof_bundle_sha256": bundle_digest,
                    "trusted_axioms": axioms,
                    "unresolved_assumptions": unresolved,
                },
            )

    claim = request["claim"]
    receipt = {
        "schema_version": RECEIPT_SCHEMA,
        "claim_digest": claim["formal_claim_digest"],
        "proof_system": "lean4",
        "toolchain": bundle["toolchain"],
        "declaration": bundle["declaration"],
        "kernel_verified": True,
        "proof_bundle_sha256": bundle_digest,
        "checker_sha256": checker_digest,
        "kernel_sha256": _sha256_file(lean),
        "auditor_sha256": _sha256_file(auditor),
        "trusted_axioms": axioms,
        "unresolved_goals": 0,
        "unresolved_assumptions": [],
    }
    return (
        "pass",
        "Lean kernel and axiom auditor accepted the pinned proof bundle",
        {
            "formal_proof": receipt,
            "build_output_sha256": _output_digest(build),
            "audit_output_sha256": _output_digest(audit),
        },
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Alexandria Lean 4 proof adapter")
    parser.add_argument("--bundle", required=True, type=Path)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--auditor", required=True, type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        request = json.load(sys.stdin)
        if not isinstance(request, dict):
            raise AdapterError("verifier request must be a JSON object")
        verdict, message, details = replay(
            request,
            bundle_path=args.bundle,
            lake=args.lake,
            lean=args.lean,
            auditor=args.auditor,
        )
        return _response(verdict, message, details)
    except (AdapterError, OSError, UnicodeError) as error:
        return _response(
            "error",
            f"Lean adapter failed closed: {type(error).__name__}: {error}",
            {},
        )


if __name__ == "__main__":
    raise SystemExit(main())

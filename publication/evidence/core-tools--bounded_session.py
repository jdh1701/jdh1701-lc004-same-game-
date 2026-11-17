"""Resumable bounded intake for Work proposals and local proposal files.

Both adapters use the existing default kernel. Neither is an LLM implementation.
Each analysis executes in a disposable process with a real wall timeout.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing
import os
import platform
import sqlite3
import sys
import tempfile
import time
from pathlib import Path

from alexandria_core.engine import AlexandriaEngine
from alexandria_core.models import canonical_json
from alexandria_core.receipts import verify_report

ROOT = Path(__file__).resolve().parents[1]


def kernel_identity():
    files = sorted((ROOT / "alexandria_core").glob("*.py")) + [Path(__file__)]
    return hashlib.sha256(canonical_json({
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in files
    }).encode()).hexdigest()


def runtime_identity():
    return {"python": sys.version, "implementation": sys.implementation.name,
            "system": platform.system(), "machine": platform.machine()}


def cache_key(kernel, runtime, scenario):
    return hashlib.sha256(canonical_json({"kernel": kernel, "runtime": runtime,
                                         "scenario": scenario}).encode()).hexdigest()


def envelope_digest(key, report):
    return hashlib.sha256(canonical_json({"key": key, "report": report}).encode()).hexdigest()


def worker(result_path, scenario):
    try:
        result = {"report": AlexandriaEngine().analyze(scenario)}
    except Exception as error:
        result = {"error": type(error).__name__ + ": " + str(error)}
    body = canonical_json(result).encode()
    if len(body) > 8 * 1024 * 1024:
        body = b'{"error":"result_size_budget"}'
    path = Path(result_path)
    temporary = path.with_suffix(".partial")
    temporary.write_bytes(body)
    os.replace(temporary, path)


def analyze_bounded(scenario, seconds):
    # Wait for process exit, not merely the first bytes of an IPC message.
    # Cleanup can add a small overhead to the analysis deadline.
    if len(canonical_json(scenario).encode()) > 1024 * 1024:
        return {"error": "input_size_budget"}
    deadline = time.monotonic() + seconds
    context = multiprocessing.get_context("spawn")
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "result.json"
        process = context.Process(target=worker, args=(str(path), scenario))
        process.start()
        try:
            process.join(timeout=max(0, deadline - time.monotonic()))
            if process.is_alive():
                return {"error": "wall_timeout"}
            if process.exitcode != 0 or not path.is_file():
                return {"error": "worker_exited_without_result"}
            return json.loads(path.read_text())
        finally:
            if process.is_alive():
                process.terminate()
            process.join(timeout=1)
            if process.is_alive():
                process.kill()
                process.join()


def run(document, database, *, adapter, max_steps=8, max_seconds=30, reverify=False):
    if adapter not in {"work", "local"}:
        raise ValueError("unknown proposal adapter")
    if type(max_steps) is not int or not 1 <= max_steps <= 128:
        raise ValueError("max_steps must be 1..128")
    if not 0 < max_seconds <= 300:
        raise ValueError("max_seconds must be positive and at most 300")
    proposals = document.get("proposals")
    if not isinstance(proposals, list) or len(proposals) > 128:
        raise ValueError("bounded proposal list required")
    start = time.monotonic()
    kernel = kernel_identity()
    runtime = runtime_identity()
    db = sqlite3.connect(database)
    db.execute("CREATE TABLE IF NOT EXISTS completed_v2 (key TEXT PRIMARY KEY, report TEXT NOT NULL, envelope_digest TEXT NOT NULL)")
    db.execute("CREATE TABLE IF NOT EXISTS attempts (id INTEGER PRIMARY KEY, key TEXT, adapter TEXT, outcome TEXT)")
    rows = []
    analyzed = 0
    stop = "queue_exhausted"
    try:
        for scenario in proposals:
            remaining = max_seconds - (time.monotonic() - start)
            if remaining <= 0 or analyzed >= max_steps:
                stop = "wall_budget" if remaining <= 0 else "step_budget"
                break
            # Full raw payload retained: never reuse under changed evidence,
            # source content, question, protocol, engine or claim identifiers.
            key = cache_key(kernel, runtime, scenario)
            previous = None if reverify else db.execute("SELECT report, envelope_digest FROM completed_v2 WHERE key=?", (key,)).fetchone()
            if previous is not None:
                report = json.loads(previous[0])
                if envelope_digest(key, report) != previous[1]:
                    raise ValueError("stored report does not bind the request/runtime envelope")
                if not verify_report(report)[0]:
                    raise ValueError("stored report failed receipt verification")
                rows.append({"key": key, "status": "already_completed",
                             "report_fingerprint": report["fingerprint"],
                             "fresh_verification": False})
                continue
            result = analyze_bounded(scenario, remaining)
            analyzed += 1
            if "report" in result:
                if not verify_report(result["report"])[0]:
                    raise ValueError("kernel report failed receipt verification")
                with db:
                    db.execute("INSERT OR REPLACE INTO completed_v2 VALUES (?,?,?)",
                               (key, canonical_json(result["report"]), envelope_digest(key, result["report"])))
            with db:
                db.execute("INSERT INTO attempts(key,adapter,outcome) VALUES (?,?,?)",
                           (key, adapter, canonical_json(result)))
            rows.append({"key": key, "status": "analyzed" if "report" in result else "failed", **result})
            if "error" in result:
                stop = "failed_attempt"
                break
        return {"schema": "alexandria-bounded-session/2", "adapter": adapter,
                "kernel_sha256": kernel, "runtime_identity": runtime, "analyzed": analyzed, "stop": stop,
                "wall_seconds": time.monotonic() - start, "rows": rows,
                "llm_generation_executed": False, "policy_changed": False}
    finally:
        db.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--adapter", choices=("work", "local"), required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("--max-steps", type=int, default=8)
    parser.add_argument("--max-seconds", type=float, default=30)
    parser.add_argument("--reverify", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run(json.loads(args.input.read_text()), args.database, adapter=args.adapter,
                 max_steps=args.max_steps, max_seconds=args.max_seconds, reverify=args.reverify)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")


if __name__ == "__main__":
    main()

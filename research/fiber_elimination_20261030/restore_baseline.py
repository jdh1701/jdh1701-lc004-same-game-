"""Restore three pinned baseline datasets after checking archive/member hashes.

Never replace a differing local file. No extractall or archive-controlled paths.
"""
from pathlib import Path
import hashlib
import json
import tarfile

ROOT = Path(__file__).resolve().parents[2]
OLD = ROOT / "research/ten_attacks_20261030"
manifest = json.loads((OLD / "evidence_manifest.json").read_text())
archive = OLD / "evidence.tar.gz"
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest["archive_sha256"]
with tarfile.open(archive, "r:gz") as tar:
    for name in ("topology", "holdout", "deep_holdout"):
        rel = f"research/ten_attacks_20261030/{name}.json"
        member = tar.getmember(rel)
        assert member.isfile()
        data = tar.extractfile(member).read()
        expected = manifest["files"][rel]
        assert len(data) == expected["bytes"]
        assert hashlib.sha256(data).hexdigest() == expected["sha256"]
        target = ROOT / rel
        if target.exists():
            assert target.read_bytes() == data, f"Refusing to replace differing {rel}"
        else:
            target.write_bytes(data)
        print("VERIFIED", rel)

"""Validate the project manifest, frozen source, and publication mappings.

This is an adapter for this repository's blueprint.toml. It is not an
upstream leanblueprint configuration parser or a replacement proof checker.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import re
import tomllib

ROOT = Path(__file__).resolve().parents[1]

def validate(config):
    assert config["schema_version"] == "alexandria-blueprint/1"
    project = config["project"]
    assert project["upstream_package"] == "leanblueprint"
    assert project["upstream_version"] == "0.0.20"
    assert (ROOT / "lean-toolchain").read_text().strip() == project["lean_toolchain"]
    receipt = json.loads((ROOT / "research/face_decomposition_verification.json").read_text())
    assert receipt["final_proof_commit"] == project["proof_commit"]
    for item in receipt["source_hashes"]:
        data = (ROOT / item["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == item["sha256"], item["path"]
    paper = (ROOT / project["paper"]).read_text()
    content = (ROOT / "blueprint/src/content.tex").read_text()
    web_labels = re.findall(r"\\label\{([^}]+)\}", content)
    assert len(web_labels) == len(set(web_labels)), "Duplicate Blueprint label"
    for label in re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", content):
        assert label in web_labels, ("Undefined Blueprint reference", label)
    for path in (project["web_entry"], project["upstream_config"]):
        assert (ROOT / path).is_file(), path
    blocks = re.findall(
        r"\\begin\{(definition|lemma|theorem|corollary)\}(.*?)\\end\{\1\}", paper, re.S)
    paired = {}
    for _, block in blocks:
        label = re.search(r"\\label\{([^}]+)\}", block)
        decls = re.search(r"\\lean\{([^}]+)\}", block)
        if label and decls:
            assert block in content, ("Blueprint statement differs from paper", label[1])
            assert label[1] not in paired
            paired[label[1]] = [x.strip() for x in decls[1].split(",")]
    declarations = {x["name"]: x for x in config["declarations"]}
    assert len(declarations) == len(config["declarations"])
    graph = {}
    for row in config["statements"]:
        assert row["status"] == "lean_verified"
        assert paired[row["label"]] == row["declarations"], row["label"]
        assert r"\label{" + row["label"] + "}" in content
        assert r"\lean{" + ",".join(row["declarations"]) + "}" in content
        graph[row["label"]] = row["uses"]
        for name in row["declarations"]:
            record = declarations[name]
            assert record["label"] == row["label"]
            source = (ROOT / record["file"]).read_text()
            assert hashlib.sha256(source.encode()).hexdigest() == record["source_sha256"]
            assert name.removeprefix("LC004.") in source.splitlines()[record["line"] - 1]
    assert set(paired) == set(graph), "Every marked manuscript statement must be registered"
    assert set(declarations) == {d for x in config["statements"] for d in x["declarations"]}
    seen, active = set(), set()
    def visit(label):
        assert label in graph, ("missing dependency", label)
        assert label not in active, ("dependency cycle", label)
        if label in seen:
            return
        active.add(label)
        for dep in graph[label]:
            visit(dep)
        active.remove(label)
        seen.add(label)
    for label in graph:
        visit(label)
    for item in config["open_obligations"]:
        assert item["status"] != "lean_verified"
        assert r"\label{" + item["label"] + "}" in paper
        assert item["label"] not in graph
    frozen = re.findall(
        r"% BEGIN FROZEN SOURCE: ([^\n]+)\n\\begin\{LeanCode\}\n(.*?)\\end\{LeanCode\}\n% END FROZEN SOURCE",
        paper, re.S)
    assert len(frozen) == 7
    for path, source in frozen:
        assert source == (ROOT / path).read_text(), ("source appendix differs", path)
    embedded = re.search(r"\\begin\{filecontents\*\}\[overwrite\]\{references.bib\}\n(.*?)\\end\{filecontents\*\}", paper, re.S)
    assert embedded and embedded[1] == (ROOT / "publication/references.bib").read_text()
    return sorted(declarations)

def write_audit(names):
    quoted = ",\n    ".join(chr(96) + name for name in names)
    text = """import LC004.HeavyFaceCertificateProduct
import Lean.Util.CollectAxioms

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env <- getEnv
  let names : List Name := [
    """ + quoted + """]
  for name in names do
    let some info := env.find? name
      | throwError "Blueprint declaration does not exist: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial Blueprint declaration: {name}"
    let axs <- collectAxioms name
    for ax in axs do
      unless ax == QUOTEpropext || ax == QUOTEClassical.choice || ax == QUOTEQuot.sound do
        throwError "Forbidden axiom {ax} in Blueprint declaration {name}"
  logInfo m!"BLUEPRINT DECLARATION AUDIT PASS: {names.length} actual declarations"
"""
    (ROOT / "publication/BlueprintDeclAudit.lean").write_text(text.replace("QUOTE", chr(96)))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    config = tomllib.loads((ROOT / "blueprint.toml").read_text())
    names = validate(config)
    if args.self_test:
        mutations = []
        bad = copy.deepcopy(config)
        bad["declarations"][0]["name"] = "LC004.face_decomposition_theorem"
        mutations.append(bad)
        bad = copy.deepcopy(config)
        bad["declarations"][0]["source_sha256"] = "0" * 64
        mutations.append(bad)
        bad = copy.deepcopy(config)
        bad["statements"][0]["uses"] = [bad["statements"][0]["label"]]
        mutations.append(bad)
        bad = copy.deepcopy(config)
        bad["open_obligations"][0]["status"] = "lean_verified"
        mutations.append(bad)
        for i, bad in enumerate(mutations):
            try:
                validate(bad)
            except (AssertionError, KeyError):
                continue
            raise AssertionError(("mutation accepted", i))
        print("MUTATION CHECK PASS: absent name, changed source, cycle, false promotion")
    write_audit(names)
    print(f"PUBLICATION MAPPING PASS: {len(names)} declarations; run Lean audit next")

if __name__ == "__main__":
    main()

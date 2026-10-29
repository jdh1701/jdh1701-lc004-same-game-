"""Package the checked Blueprint, source ledger, PDF, and downloadable sources."""
from pathlib import Path
import hashlib
import html
import json
import shutil
from importlib.metadata import version
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import tomllib
import zipfile
from pypdf import PdfReader
from validate_blueprint import ROOT, validate

config = tomllib.loads((ROOT / "blueprint.toml").read_text())
names = validate(config)
actual = (ROOT / "blueprint/lean_decls").read_text().splitlines()
assert set(actual) == set(names), "Rendered declaration list differs from manifest"
web = ROOT / "blueprint/web"
assert (web / "index.html").is_file()
assert (web / "dep_graph_document.html").stat().st_size > 1000
pages = list(web.glob("*.html"))
page_text = {p.name: p.read_text() for p in pages}
for row in config["statements"]:
    assert any(row["label"] in text for text in page_text.values()), row["label"]
pdf = ROOT / "publication/paper.pdf"
page_count = len(PdfReader(pdf).pages)
assert 35 <= page_count <= 55, page_count
log = (ROOT / "publication/paper.log").read_text()
assert "Missing character:" not in log
assert "Overfull" not in log
assert "There were undefined references" not in log
assert "Citation" not in log or "undefined" not in log
site = ROOT / "_site"
if site.exists():
    shutil.rmtree(site)
site.mkdir()
shutil.copytree(web, site / "blueprint")
shutil.copy2(pdf, site / "paper.pdf")
for p in ("paper.tex", "references.bib"):
    shutil.copy2(ROOT / "publication" / p, site / p)
shutil.copy2(ROOT / "blueprint.toml", site / "blueprint.toml")
sha = config["project"]["proof_commit"]
repo = "https://github.com/" + config["project"]["repository"]
urls = {d["name"]: f'{repo}/blob/{sha}/{d["file"]}#L{d["line"]}'
        for d in config["declarations"]}
find = site / "docs/find"
find.mkdir(parents=True)
(find / "index.html").write_text("""<!doctype html><html lang="en"><meta charset="utf-8">
<title>Checked Lean declaration</title><body><p id="message">Resolving declaration...</p>
<script>
const urls = """ + json.dumps(urls) + """;
const name = decodeURIComponent(location.hash.replace(/^#doc\\//, ""));
const message = document.getElementById("message");
if (Object.hasOwn(urls, name)) {
  const a = document.createElement("a"); a.href = urls[name]; a.textContent = name;
  message.replaceChildren(a); location.replace(urls[name]);
} else { message.textContent = "Unknown declaration: " + name; }
</script></body></html>""")
rows = []
for row in config["statements"]:
    page = next(p for p, text in page_text.items() if f'id="{row["label"]}"' in text)
    decl_links = "<br>".join(
        f'<a href="{html.escape(urls[n])}">{html.escape(n)}</a>' for n in row["declarations"])
    rows.append(f'<tr><td><a href="blueprint/{page}#{html.escape(row["label"])}">'
                f'{html.escape(row["label"])}</a></td><td>Lean verified</td><td>{decl_links}</td></tr>')
(site / "index.html").write_text("""<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Alexandria Omega — LC004 proof ledger</title>
<style>body{font:17px/1.55 system-ui,sans-serif;max-width:1100px;margin:3rem auto;padding:0 1.2rem;color:#182025}
h1{line-height:1.15}a{color:#174c8b}table{width:100%;border-collapse:collapse;font-size:14px}
td,th{padding:.7rem;text-align:left;border-bottom:1px solid #ddd;overflow-wrap:anywhere}
input{padding:.7rem;width:95%;margin:1rem 0}code{overflow-wrap:anywhere}.note{border-left:4px solid #777;padding-left:1rem}
</style><h1>Alexandria Ω<br>Verified Same Game face decomposition</h1>
<p>John D. Holden III · 2026</p>
<p><a href="paper.pdf">Technical paper (""" + str(page_count) + """ pages)</a> ·
<a href="blueprint/index.html">Interactive Blueprint</a> ·
<a href="blueprint/dep_graph_document.html">Dependency graph</a> ·
<a href="sources.zip">Complete publication sources</a></p>
<p class="note">Verified: the structural criterion for linear maximal-run deletion and the
certificate partition product. Open: unrestricted winning-word enumeration, Lean slot/profile
correspondence, and ring-game semantic transfer. Counterexample minimality is computational.</p>
<p>Mathematical proof snapshot: <code>""" + sha + """</code>.
<a href="https://github.com/jdh1701/jdh1701-lc004-same-game-/actions/runs/40831342439">Frozen proof CI</a>.</p>
<label for="filter">Filter theorem labels or Lean declarations</label>
<input id="filter" type="search" placeholder="Try face, assembly, or locality">
<table><thead><tr><th>Statement</th><th>Status</th><th>Exact Lean source</th></tr></thead><tbody>"""
+ "\n".join(rows) + """</tbody></table>
<p><a href="blueprint.toml">Project manifest</a> · <a href="publication-manifest.json">Artifact hashes</a>.
The TOML manifest is a repository adapter; upstream leanblueprint uses TeX and plastex.cfg.</p>
<script>document.getElementById("filter").addEventListener("input", e => {
const q=e.target.value.toLowerCase();document.querySelectorAll("tbody tr").forEach(r=>{
r.hidden=!r.textContent.toLowerCase().includes(q);});});</script></html>""")
source_files = [
    ROOT / "blueprint.toml",
    ROOT / ".github/workflows/publication-blueprint.yml",
    *sorted((ROOT / "blueprint/src").rglob("*.tex")),
    ROOT / "blueprint/src/plastex.cfg", ROOT / "blueprint/src/latexmkrc",
]
source_files += [p for p in (ROOT / "publication").rglob("*") if p.is_file()
                 and p.suffix in {".tex", ".bib", ".py", ".lean", ".json", ".md", ".txt"}
                 and "build" not in p.parts and "__pycache__" not in p.parts]
source_files = sorted(set(source_files))
manifest = {
    "schema": "alexandria-publication-artifacts/1",
    "proof_commit": sha,
    "page_count": page_count,
    "blueprint_statements": len(config["statements"]),
    "checked_declarations": len(names),
    "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
    "python_dependencies": {
        line.split("==", 1)[0]: version(line.split("==", 1)[0])
        for line in (ROOT / "publication/requirements.txt").read_text().splitlines()
        if "==" in line and not line.startswith("#")},
    "entries": [{"path": str(p.relative_to(ROOT)),
                 "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in source_files],
    "limitations": ["TOML is a project adapter, not upstream canonical configuration",
                    "Mathematical proof and architecture proposal have distinct assurance",
                    "Deployment success is recorded separately from build success"],
}
(site / "publication-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
zip_path = ROOT / "publication/Alexandria_Omega_Publication_Sources.zip"
with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
    for p in source_files:
        info = zipfile.ZipInfo(str(p.relative_to(ROOT)), (2026, 10, 29, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        z.writestr(info, p.read_bytes())
    info = zipfile.ZipInfo("publication-manifest.json", (2026, 10, 29, 0, 0, 0))
    info.compress_type = zipfile.ZIP_DEFLATED
    info.external_attr = 0o100644 << 16
    z.writestr(info, json.dumps(manifest, indent=2) + "\n")
shutil.copy2(zip_path, site / "sources.zip")
(site / ".nojekyll").write_text("")

class LocalLinks(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links, self.ids = [], set()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])

parsed = {}
for path in site.rglob("*.html"):
    parser = LocalLinks()
    parser.feed(path.read_text())
    parsed[path.resolve()] = parser
link_count = 0
for path, parser in parsed.items():
    for link in parser.links:
        url = urlsplit(link)
        if url.scheme or url.netloc:
            continue
        target = (path.parent / unquote(url.path)).resolve() if url.path else path
        if target.is_dir():
            target = target / "index.html"
        assert target.is_relative_to(site.resolve()), ("Link escapes site", link)
        assert target.is_file(), ("Broken local link", path, link)
        if url.fragment and target in parsed and not url.fragment.startswith("doc/"):
            assert unquote(url.fragment) in parsed[target].ids, ("Missing anchor", link)
        link_count += 1
print(f"LOCAL LINK AUDIT PASS: {link_count} links")
print(f"SITE BUILD PASS: {page_count} pages, {len(names)} checked declaration links")

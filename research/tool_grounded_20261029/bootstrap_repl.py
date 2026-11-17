"""Build an isolated, source-hash-pinned official Lean REPL."""
from pathlib import Path
import argparse,hashlib,json,subprocess,urllib.request
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--directory',type=Path,required=True)
args=parser.parse_args();manifest=json.loads((ROOT/'repl-source-manifest.json').read_text())
args.directory.mkdir(parents=True,exist_ok=True)
for row in manifest['files']:
    path=args.directory/row['path']
    if path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256']:
        continue
    url=f"https://raw.githubusercontent.com/{manifest['repository']}/{manifest['commit']}/{row['path']}"
    content=urllib.request.urlopen(url,timeout=30).read()
    assert hashlib.sha256(content).hexdigest()==row['sha256'],row['path']
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(content)
assert (args.directory/'lean-toolchain').read_text().strip()==manifest['lean']
subprocess.run(['lake','build'],cwd=args.directory,check=True)
print(args.directory/'.lake/build/bin/repl')

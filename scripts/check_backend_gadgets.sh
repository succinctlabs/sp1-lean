#!/usr/bin/env bash
# Explicit setup: npm ci --prefix tools/backend-gadgets. This checker never installs tools.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $# != 0 ]]; then
  echo 'usage: scripts/check_backend_gadgets.sh' >&2
  exit 2
fi
for prerequisite in node python3 elan git; do
  if ! command -v "$prerequisite" >/dev/null 2>&1; then
    echo "Missing $prerequisite; see tools/backend-gadgets/README.md for explicit setup." >&2
    exit 2
  fi
done
if [[ $(node --version) != v22.16.0 ]]; then
  echo 'Expected Node v22.16.0; activate the pinned version before running.' >&2
  exit 2
fi
cli=tools/backend-gadgets/node_modules/snarkjs/build/cli.cjs
if [[ ! -f $cli ]]; then
  echo 'Missing pinned snarkjs. Run: npm ci --prefix tools/backend-gadgets' >&2
  exit 2
fi
node -e 'const p=require("./tools/backend-gadgets/node_modules/snarkjs/package.json"); if(p.version!=="0.7.6") throw Error("Expected snarkjs 0.7.6; run npm ci --prefix tools/backend-gadgets")'
toolchain=$(cat lean-toolchain)
if ! elan run "$toolchain" lean --version >/dev/null 2>&1; then
  echo "Missing $toolchain. Install it explicitly with: elan toolchain install '$toolchain'" >&2
  exit 2
fi
python3 - <<'PY'
import json
from pathlib import Path
import re
import subprocess
manifest=json.loads(Path('lake-manifest.json').read_text())
artifacts=json.loads(Path('export/backend-gadgets/manifest.json').read_text())
clean=next(package for package in manifest['packages'] if package['name']=='Clean')
if artifacts['cleanRevision'] != clean['rev']:
    raise SystemExit('Backend artifact provenance does not match the resolved Clean revision')
package=json.loads(Path('tools/backend-gadgets/package.json').read_text())
lock=json.loads(Path('tools/backend-gadgets/package-lock.json').read_text())
if (package['dependencies']['snarkjs'] != '0.7.6' or
    lock['packages']['node_modules/snarkjs']['version'] != '0.7.6' or artifacts['snarkjs'] != '0.7.6'):
    raise SystemExit('Expected snarkjs 0.7.6 in package, lockfile, and artifact provenance')
by_name={package['name']: package for package in manifest['packages']}
for block in re.split(r'\[\[require\]\]', Path('lakefile.toml').read_text())[1:]:
    body=re.split(r'\n\[\[', block)[0]
    name=re.search(r'^name = "([^"]+)"', body, re.M)
    revision=re.search(r'^rev = "([^"]+)"', body, re.M)
    url=re.search(r'^git = "([^"]+)"', body, re.M)
    if name and revision and url:
        resolved=by_name.get(name[1], {})
        if (revision[1] not in (resolved.get('inputRev'), resolved.get('rev')) or
            url[1] != resolved.get('url')):
            raise SystemExit(f"{name[1]}: lakefile and resolved manifest disagree; prepare dependencies explicitly")
for package in manifest['packages']:
    directory=Path(manifest['packagesDir']) / package['name']
    if package['type'] != 'git' or not (directory / '.git').exists():
        raise SystemExit(f"Missing pinned {package['name']}; prepare dependencies explicitly before running")
    revision=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
    if revision != package['rev']:
        raise SystemExit(f"{package['name']}: expected pinned revision {package['rev']}, found {revision}")
    dirty=subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no'],text=True)
    if dirty:
        raise SystemExit(f"{package['name']}: dependency has tracked local edits")
PY
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} elan run "$toolchain" lake --no-cache build --wfail --iofail backendGadgets
scratch=$(mktemp -d .lake/backend-gadgets.XXXXXX)
trap 'rm -rf "$scratch"' EXIT
.lake/build/bin/backendGadgets "$scratch/generated"
python3 - "$scratch/generated" <<'PY'
from pathlib import Path
import sys
generated=Path(sys.argv[1]); committed=Path('export/backend-gadgets')
files=lambda root: {p.relative_to(root) for p in root.rglob('*') if p.is_file()}
if files(generated) != files(committed):
    raise SystemExit('Backend artifact inventory differs; regenerate with .lake/build/bin/backendGadgets export/backend-gadgets')
for path in sorted(files(generated)):
    if (generated/path).read_bytes() != (committed/path).read_bytes():
        raise SystemExit(f'Backend artifact differs: {path}')
print('PASS deterministic backend artifact regeneration')
PY
python3 scripts/check_backend_gadgets.py "$scratch/generated" "$scratch/witnesses" --cli "$cli"

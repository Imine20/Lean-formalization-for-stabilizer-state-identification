#!/usr/bin/env python3
"""Install the SHA-256-pinned Lean compiler for a supported host platform."""
from pathlib import Path
import hashlib, json, platform, subprocess
root = Path(__file__).resolve().parents[1]
lock = json.loads((root/'toolchain-lock.json').read_text())
host_key = platform.system() + '-' + platform.machine()
asset = lock.get('compiler_assets', {}).get(host_key)
if asset is None:
    raise SystemExit('No compiler asset lock for ' + host_key)
folder = root/'.toolchain'
folder.mkdir(exist_ok=True)
archive = folder/(asset['directory'] + '.tar.zst')
if not archive.exists():
    subprocess.run(['curl','--fail','--location','--retry','2',asset['url'],'-o',str(archive)],check=True)
with archive.open('rb') as stream:
    digest = hashlib.sha256()
    for chunk in iter(lambda: stream.read(1024 * 1024), b''):
        digest.update(chunk)
    actual = digest.hexdigest()
if actual != asset['sha256']:
    raise SystemExit('Compiler archive SHA-256 mismatch; retained for inspection')
compiler = folder/asset['directory']/'bin/lean'
if not compiler.exists():
    subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(folder)],check=True)
version = subprocess.check_output([str(compiler),'--version'],text=True).strip()
if lock['lean_commit'] not in version:
    raise SystemExit('Compiler commit mismatch: '+version)
print(version)
print('Pinned compiler archive verified. Next: python3 scripts/reproduce.py --require-main-proof --dest /tmp/stabilizer-fresh')

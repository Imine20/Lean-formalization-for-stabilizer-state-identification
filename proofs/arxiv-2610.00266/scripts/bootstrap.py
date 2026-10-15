#!/usr/bin/env python3
"""Install exactly the locked compiler. Does not execute paper code."""
import hashlib,json,pathlib,platform,subprocess
root=pathlib.Path(__file__).resolve().parents[1]
lock=json.loads((root/'locks/toolchain.json').read_text())
asset=lock['compiler_assets'][platform.system()+'-'+platform.machine()]
folder=root/'.toolchain'; folder.mkdir(exist_ok=True)
archive=folder/(asset['directory']+'.tar.zst')
if not archive.exists():
    subprocess.run(['curl','--fail','--location','--retry','2',asset['url'],'-o',str(archive)],check=True)
with archive.open('rb') as stream:
    hasher = hashlib.sha256()
    for chunk in iter(lambda: stream.read(1024 * 1024), b''):
        hasher.update(chunk)
    digest = hasher.hexdigest()
if digest!=asset['sha256']: raise SystemExit('Compiler archive hash mismatch')
compiler=folder/asset['directory']/'bin/lean'
if not compiler.exists(): subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(folder)],check=True)
version=subprocess.check_output([str(compiler),'--version'],text=True).strip()
if lock['lean_commit'] not in version: raise SystemExit('Compiler commit mismatch')
print(version)

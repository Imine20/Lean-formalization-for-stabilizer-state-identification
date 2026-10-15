#!/usr/bin/env python3
"""Read-only extra isolation and received-evidence checks on the existing cloud build."""
from pathlib import Path
import datetime, hashlib, json, subprocess

ROOT = Path('/data/lean/tasks/graded-integration')
FRESH = Path('/data/lean/StabilizerLearning-clean-20261011-graded-583897b83f27')
STAGE = ROOT/'docs/validation/2026-10-11-graded-verification'
FROZEN = '583897b83f2714c9b1a4d27fb1cfd2fc988ee7e8'

def out(args, cwd=None):
    return subprocess.check_output(args,cwd=cwd,text=True).strip()

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):
            digest.update(chunk)
    return digest.hexdigest()

assert json.loads((STAGE/'comparison.json').read_text())['result'] == 'pass'
fresh = json.loads((FRESH/'reproduction.json').read_text())
assert fresh['result'] == 'pass' and fresh['git_commit'] == FROZEN
manifest = json.loads((ROOT/'lake-manifest.json').read_text())
packages = FRESH/'project/.lake/packages'
rows = []
for pkg in manifest['packages']:
    folder = packages/pkg['name']
    rows.append({
        'name':pkg['name'],'expected_rev':pkg['rev'],
        'actual_rev':out(['git','rev-parse','HEAD'],folder),
        'tracked_status':out(['git','status','--porcelain','--untracked-files=no'],folder),
        'directory_is_symlink':folder.is_symlink(),
        'git_objects_alternates_present':(folder/'.git/objects/info/alternates').exists(),
        'tracked_olean_files':out(['git','ls-files','*.olean'],folder)
    })
names = ['comparison.json','dependency-checkouts.json','source-preservation.json',
         'execution/check.json','execution/clean-preflight.json',
         'execution/axioms.log','execution/build.log','execution/main-release-gate.log',
         'fresh/reproduction.json','fresh/axioms.log','fresh/build.log','fresh/main-release-gate.log',
         'new-proof-links.log','new-proof-links-initial.log']
archive = Path('/home/ubuntu/lean-formalization/.toolchain/lean-4.24.0-linux.tar.zst')
compiler = archive.parent/'lean-4.24.0-linux/bin/lean'
result = {
    'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'frozen_commit':FROZEN,
    'fresh_directory':str(FRESH),
    'packages_directory_is_symlink':packages.is_symlink(),
    'cache_directory_is_symlink':(FRESH/'mathlib-cache').is_symlink(),
    'packages':rows,
    'compiler_version':out([str(compiler),'--version']),
    'compiler_archive_actual_sha256':sha(archive),
    'evidence_sha256':{name:sha(STAGE/name) for name in names},
    'storage':out(['df','-h','/','/data']),
    'memory':out(['free','-h']),
    'resource_policy':'Existing peer-owned two cloud checks reused; no third cloud clone or build. Mac is the independent platform check.'
}
print(json.dumps(result,indent=2))

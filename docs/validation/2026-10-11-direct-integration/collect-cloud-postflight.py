#!/usr/bin/env python3
"""Read-only isolation, exact-dependency and received-evidence checks after success."""
from pathlib import Path
import datetime, hashlib, json, subprocess
ROOT=Path('/data/lean/tasks/direct-final-6d17da2')
FRESH=Path('/data/lean/StabilizerLearning-clean-20261011-direct-6d17da2')
FROZEN='6d17da20d7a7625333ecf87d23824f031a01a6ae'
def out(args,cwd=None):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
fresh=json.loads((FRESH/'reproduction.json').read_text())
assert fresh['result']=='pass' and fresh['git_commit']==FROZEN and fresh['main_theorem_complete']
manifest=json.loads((ROOT/'lake-manifest.json').read_text())
packages=FRESH/'project/.lake/packages'
rows=[]
for pkg in manifest['packages']:
 folder=packages/pkg['name']
 rows.append({'name':pkg['name'],'expected_rev':pkg['rev'],
  'actual_rev':out(['git','rev-parse','HEAD'],folder),
  'tracked_status':out(['git','status','--porcelain','--untracked-files=no'],folder),
  'directory_is_symlink':folder.is_symlink(),
  'git_objects_alternates_present':(folder/'.git/objects/info/alternates').exists(),
  'tracked_olean_files':out(['git','ls-files','*.olean'],folder)})
archive=Path('/home/ubuntu/lean-formalization/.toolchain/lean-4.24.0-linux.tar.zst')
compiler=archive.parent/'lean-4.24.0-linux/bin/lean'
names=['reproduction.json','logs/build.log','logs/axioms.log','logs/main-release-gate.log','logs/cache.log']
result={'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'frozen_commit':FROZEN,'fresh_directory':str(FRESH),
 'packages_directory_is_symlink':packages.is_symlink(),
 'cache_directory_is_symlink':(FRESH/'mathlib-cache').is_symlink(),
 'packages':rows,'compiler_version':out([str(compiler),'--version']),
 'compiler_archive_actual_sha256':sha(archive),
 'evidence_sha256':{n:sha(FRESH/n) for n in names},
 'storage':out(['df','-h','/','/data']),'memory':out(['free','-h']),
 'resource_policy':'One final whole-proof Linux fresh reproduction on /data; separate Mac whole-root clean check. Earlier PGM-only runs are supplementary, not identical-source final acceptance.'}
print(json.dumps(result,indent=2))

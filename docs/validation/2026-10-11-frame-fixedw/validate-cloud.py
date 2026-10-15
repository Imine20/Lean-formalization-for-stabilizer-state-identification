#!/usr/bin/env python3
"""Run this milestone from a detached private-source clone and a fresh build tree."""
import argparse, datetime, hashlib, json, os, pathlib, subprocess
p=argparse.ArgumentParser();p.add_argument('commit');a=p.parse_args()
source=pathlib.Path('/data/lean/tasks/frame-validation-source-'+a.commit[:12])
dest=pathlib.Path('/data/lean/StabilizerLearning-clean-20261011-frame-'+a.commit[:12])
assert len(a.commit)==40 and all(c in '0123456789abcdef' for c in a.commit)
assert not source.exists() and not dest.exists(), 'Fresh paths required'
subprocess.run(['git','clone','--no-hardlinks','/home/ubuntu/git/StabilizerLearning.git',str(source)],check=True)
subprocess.run(['git','checkout','--detach',a.commit],cwd=source,check=True)
(source/'.toolchain').symlink_to('/home/ubuntu/lean-formalization/.toolchain',target_is_directory=True)
def out(args,cwd=None):return subprocess.check_output(args,cwd=cwd,text=True).strip()
assert out(['git','status','--short'],source)==''
compiler=source/'.toolchain/lean-4.24.0-linux/bin/lean'
archive=source/'.toolchain/lean-4.24.0-linux.tar.zst'
digest=hashlib.sha256()
with archive.open('rb') as f:
    for chunk in iter(lambda: f.read(1024*1024),b''): digest.update(chunk)
archive_sha=digest.hexdigest()
lock=json.loads((source/'toolchain-lock.json').read_text())
assert archive_sha==lock['compiler_assets']['Linux-x86_64']['sha256']
preflight={'source_directory':str(source),'host':'lean-server','frozen_git_commit':a.commit,
 'compiler_version':out([str(compiler),'--version']),'compiler_archive_actual_sha256':archive_sha,
 'reproduction_directory':str(dest),'vcpus':os.cpu_count(),
 'storage_before':out(['df','-h','/','/data']), 'memory_before':out(['free','-h']),
 'network':'Task-scoped six proxy variables; own loopback SSH reverse tunnel 17894 to existing Mac proxy 7890. No global changes.',
 'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
result=subprocess.run(['python3','scripts/reproduce.py','--dest',str(dest)],cwd=source)
logs=dest/'logs';logs.mkdir(exist_ok=True)
(logs/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
metrics=dest/'reproduction.json'
if metrics.exists(): (logs/'reproduction.json').write_bytes(metrics.read_bytes())
assert result.returncode==0, 'Fresh reproduction failed; original logs retained'
project=dest/'project';packages=project/'.lake/packages';manifest=json.loads((project/'lake-manifest.json').read_text())
rows=[]
for pkg in manifest['packages']:
    folder=packages/pkg['name']
    rows.append({'name':pkg['name'],'expected_rev':pkg['rev'],'actual_rev':out(['git','rev-parse','HEAD'],folder),
      'tracked_status':out(['git','status','--porcelain','--untracked-files=no'],folder),
      'directory_is_symlink':folder.is_symlink(),
      'git_objects_alternates_present':(folder/'.git/objects/info/alternates').exists(),
      'tracked_olean_files':out(['git','ls-files','*.olean'],folder)})
isolation={'source_commit':out(['git','rev-parse','HEAD'],source),
 'source_worktree_status':out(['git','status','--short'],source),
 'packages_directory_is_symlink':packages.is_symlink(),
 'mathlib_cache_is_symlink':(dest/'mathlib-cache').is_symlink(),
 'packages':rows,'storage_after':out(['df','-h','/','/data'])}
(logs/'isolation.json').write_text(json.dumps(isolation,indent=2)+'\n')
checks={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in logs.iterdir() if f.is_file()}
(logs/'evidence-sha256.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'result':'pass','destination':str(dest),'evidence':str(logs)},indent=2))
